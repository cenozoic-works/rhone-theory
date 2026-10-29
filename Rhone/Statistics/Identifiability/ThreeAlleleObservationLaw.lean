/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeAlleleMutationBridge
public import Rhone.Statistics.Identifiability.IndependentClockObservation

/-! # The ordered four-allele law for the three-allele mutation model -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

namespace Rhone.Statistics.Identifiability.ThreeAlleleMutation

open FiniteSiteObservation (AllelePair Observation NonnegativeTimes)

def conditionalKernel (k : ℝ) (t : ℝ × ℝ) (a : Observation 3) : ℝ :=
  siteKernel k t.1 a.1 * siteKernel k t.2 a.2

def mass (k : ℝ) (ν : Measure (ℝ × ℝ)) (a : Observation 3) : ℝ :=
  ∫ t, conditionalKernel k t a ∂ν

def law (k : ℝ) (ν : Measure (ℝ × ℝ)) : Measure (Observation 3) :=
  Measure.sum fun a => ENNReal.ofReal (mass k ν a) • Measure.dirac a

lemma conditionalKernel_sum (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation 3, conditionalKernel k t a = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalKernel, ← Finset.mul_sum, siteKernel_sum, mul_one]

@[fun_prop] lemma conditionalKernel_measurable (k : ℝ) (a : Observation 3) :
    Measurable (fun t => conditionalKernel k t a) := by
  exact ((siteKernel_measurable k a.1).comp measurable_fst).mul
    ((siteKernel_measurable k a.2).comp measurable_snd)

lemma conditionalKernel_bounds {k : ℝ} (hk : 0 ≤ k)
    {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) (a : Observation 3) :
    0 ≤ conditionalKernel k t a ∧ conditionalKernel k t a ≤ 1 := by
  exact ⟨mul_nonneg (siteKernel_nonneg hk ht.1 _) (siteKernel_nonneg hk ht.2 _),
    (mul_le_of_le_one_left (siteKernel_nonneg hk ht.2 _) (siteKernel_le_one hk ht.1 _)).trans
        (siteKernel_le_one hk ht.2 _)⟩

lemma conditionalKernel_integrable {k : ℝ} {ν : Measure (ℝ × ℝ)}
    [IsFiniteMeasure ν] (hk : 0 ≤ k) (hν : NonnegativeTimes ν)
    (a : Observation 3) : Integrable (fun t => conditionalKernel k t a) ν := by
  refine Integrable.of_bound (conditionalKernel_measurable k a).aestronglyMeasurable 1 ?_
  filter_upwards [hν] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (conditionalKernel_bounds hk ht a).1]
  exact (conditionalKernel_bounds hk ht a).2

lemma mass_nonneg {k : ℝ} {ν : Measure (ℝ × ℝ)}
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) (a : Observation 3) :
    0 ≤ mass k ν a := by
  apply integral_nonneg_of_ae
  filter_upwards [hν] with t ht
  exact (conditionalKernel_bounds hk ht a).1

lemma mass_sum {k : ℝ} {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    ∑ a : Observation 3, mass k ν a = 1 := by
  unfold mass
  rw [← integral_finsetSum _ (fun a _ => conditionalKernel_integrable hk hν a)]
  simp_rw [conditionalKernel_sum]
  simp

lemma law_singleton (k : ℝ) (ν : Measure (ℝ × ℝ)) (a : Observation 3) :
    law k ν {a} = ENNReal.ofReal (mass k ν a) := by
  simp [law, Pi.single_apply, mul_ite]

theorem law_probability {k : ℝ} {ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure ν] (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    IsProbabilityMeasure (law k ν) := by
  constructor
  simp only [law, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mass_nonneg hk hν a),
    mass_sum hk hν, ENNReal.ofReal_one]

lemma score_integrable (ν : Measure (Observation 3)) [IsFiniteMeasure ν]
    (f : Observation 3 → ℝ) : Integrable f ν := Integrable.of_finite

lemma integral_law_eq_integral_sum {k : ℝ} {ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure ν] (hk : 0 ≤ k) (hν : NonnegativeTimes ν)
    (f : Observation 3 → ℝ) :
    (∫ a, f a ∂law k ν) =
      ∫ t, ∑ a : Observation 3, conditionalKernel k t a * f a ∂ν := by
  let := law_probability hk hν
  rw [integral_fintype (score_integrable _ f)]
  simp only [Measure.real, law_singleton, ENNReal.toReal_ofReal (mass_nonneg hk hν _),
    smul_eq_mul]
  rw [integral_finsetSum _ (fun a _ => (conditionalKernel_integrable hk hν a).mul_const (f a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_mul_const]
  rfl

def vA (a : Observation 3) : ℝ := modeV a.1.1 * modeV a.1.2

def vB (a : Observation 3) : ℝ := modeV a.2.1 * modeV a.2.2

def wB (a : Observation 3) : ℝ := modeW a.2.1 * modeW a.2.2

def vAvB (a : Observation 3) : ℝ := vA a * vB a

def vAwB (a : Observation 3) : ℝ := vA a * wB a

lemma conditional_vA (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation 3, conditionalKernel k t a * vA a =
      (2/3 : ℝ) * Real.exp (-(5*k)*t.1) := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalKernel, vA]
  simp_rw [mul_right_comm (siteKernel k t.1 _) _ (modeV _ * modeV _)]
  simp only [← Finset.mul_sum, siteKernel_sum, mul_one]
  exact siteKernel_contrastV k t.1

lemma conditional_vB (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation 3, conditionalKernel k t a * vB a =
      (2/3 : ℝ) * Real.exp (-(5*k)*t.2) := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalKernel, vB, mul_assoc, ← Finset.mul_sum,
    siteKernel_contrastV]
  rw [← Finset.sum_mul, siteKernel_sum, one_mul]

lemma conditional_pair_score (k : ℝ) (t : ℝ × ℝ)
    (f g : AllelePair 3 → ℝ) :
    (∑ a : Observation 3, conditionalKernel k t a * (f a.1 * g a.2)) =
      (∑ x : AllelePair 3, siteKernel k t.1 x * f x) *
      (∑ y : AllelePair 3, siteKernel k t.2 y * g y) := by
  rw [Fintype.sum_prod_type]
  simp only [conditionalKernel]
  have h (x y : AllelePair 3) :
      siteKernel k t.1 x * siteKernel k t.2 y * (f x * g y) =
        (siteKernel k t.1 x * f x) * (siteKernel k t.2 y * g y) := by ring
  simp_rw [h]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

lemma conditional_vAvB (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation 3, conditionalKernel k t a * vAvB a =
      (4/9 : ℝ) * (Real.exp (-(5*k)*t.1) * Real.exp (-(5*k)*t.2)) := by
  unfold vAvB vA vB
  rw [conditional_pair_score k t (fun x => modeV x.1 * modeV x.2)
    (fun y => modeV y.1 * modeV y.2), siteKernel_contrastV, siteKernel_contrastV]
  ring

lemma conditional_vAwB (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation 3, conditionalKernel k t a * vAwB a =
      (4/3 : ℝ) * (Real.exp (-(5*k)*t.1) * Real.exp (-(3*k)*t.2)) := by
  unfold vAwB vA wB
  rw [conditional_pair_score k t (fun x => modeV x.1 * modeV x.2)
    (fun y => modeW y.1 * modeW y.2), siteKernel_contrastV, siteKernel_contrastW]
  ring

theorem vA_mean {k : ℝ} {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    (∫ a, vA a ∂law k ν) = (2/3 : ℝ) * IndependentClockObservation.laplace ν (5*k) 0 := by
  rw [integral_law_eq_integral_sum hk hν]
  simp_rw [conditional_vA]
  rw [integral_const_mul]
  simp [IndependentClockObservation.laplace, neg_mul]

theorem vB_mean {k : ℝ} {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    (∫ a, vB a ∂law k ν) = (2/3 : ℝ) * IndependentClockObservation.laplace ν 0 (5*k) := by
  rw [integral_law_eq_integral_sum hk hν]
  simp_rw [conditional_vB]
  rw [integral_const_mul]
  simp [IndependentClockObservation.laplace, neg_mul]

theorem vAvB_mean {k : ℝ} {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    (∫ a, vAvB a ∂law k ν) =
      (4/9 : ℝ) * IndependentClockObservation.laplace ν (5*k) (5*k) := by
  rw [integral_law_eq_integral_sum hk hν]
  simp_rw [conditional_vAvB]
  rw [integral_const_mul]
  simp [IndependentClockObservation.laplace, neg_mul]

theorem vAwB_mean {k : ℝ} {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hν : NonnegativeTimes ν) :
    (∫ a, vAwB a ∂law k ν) =
      (4/3 : ℝ) * IndependentClockObservation.laplace ν (5*k) (3*k) := by
  rw [integral_law_eq_integral_sum hk hν]
  simp_rw [conditional_vAwB]
  rw [integral_const_mul]
  simp [IndependentClockObservation.laplace, neg_mul]

theorem laplace_eq_of_law_eq {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (heq : law k μ = law k ν) :
    IndependentClockObservation.laplace μ (5*k) 0 =
      IndependentClockObservation.laplace ν (5*k) 0 ∧
    IndependentClockObservation.laplace μ 0 (5*k) =
      IndependentClockObservation.laplace ν 0 (5*k) ∧
    IndependentClockObservation.laplace μ (5*k) (5*k) =
      IndependentClockObservation.laplace ν (5*k) (5*k) ∧
    IndependentClockObservation.laplace μ (5*k) (3*k) =
      IndependentClockObservation.laplace ν (5*k) (3*k) := by
  have hA := congrArg (fun ρ : Measure (Observation 3) => ∫ a, vA a ∂ρ) heq
  have hB := congrArg (fun ρ : Measure (Observation 3) => ∫ a, vB a ∂ρ) heq
  have hVV := congrArg (fun ρ : Measure (Observation 3) => ∫ a, vAvB a ∂ρ) heq
  have hVW := congrArg (fun ρ : Measure (Observation 3) => ∫ a, vAwB a ∂ρ) heq
  rw [vA_mean hk hμ, vA_mean hk hν] at hA
  rw [vB_mean hk hμ, vB_mean hk hν] at hB
  rw [vAvB_mean hk hμ, vAvB_mean hk hν] at hVV
  rw [vAwB_mean hk hμ, vAwB_mean hk hν] at hVW
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Rhone.Statistics.Identifiability.ThreeAlleleMutation
