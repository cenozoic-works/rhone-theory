/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteSiteObservationCharacterization

/-! # Independent positive mutation clocks for the two sites -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Rhone.Statistics.Identifiability
namespace IndependentClockObservation
open FiniteSiteObservation

def clockScale (a b : ℝ) (t : ℝ × ℝ) : ℝ × ℝ := (a*t.1,b*t.2)

@[fun_prop] theorem clockScale_measurable (a b : ℝ) : Measurable (clockScale a b) := by
  unfold clockScale
  fun_prop

def law (K : ℕ) (a b : ℝ) (μ : Measure (ℝ × ℝ)) : Measure (Observation K) :=
  FiniteSiteObservation.law K 1 (μ.map (clockScale a b))

lemma scaled_nonnegative {a b : ℝ} {μ : Measure (ℝ × ℝ)}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hμ : NonnegativeTimes μ) :
    NonnegativeTimes (μ.map (clockScale a b)) := by
  apply (ae_map_iff (clockScale_measurable a b).aemeasurable
    (show MeasurableSet {t : ℝ × ℝ | 0 ≤ t.1 ∧ 0 ≤ t.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [hμ] with t ht
  exact ⟨mul_nonneg ha ht.1, mul_nonneg hb ht.2⟩

theorem law_eq_semigroup {K : ℕ} (hK : 2 ≤ K) (a b : ℝ)
    (μ : Measure (ℝ × ℝ)) :
    law K a b μ = Measure.sum (fun s : Observation K =>
      ENNReal.ofReal (∫ t,
        EqualRatesMutation.ancestralPair K a t.1 s.1.1 s.1.2 *
        EqualRatesMutation.ancestralPair K b t.2 s.2.1 s.2.2 ∂μ) • Measure.dirac s) := by
  unfold law FiniteSiteObservation.law mass
  congr 1
  funext s
  rw [integral_map (clockScale_measurable a b).aemeasurable
    (conditionalKernel_measurable K 1 s).aestronglyMeasurable]
  simp_rw [EqualRatesMutation.ancestralPair_eq_siteKernel hK]
  simp [conditionalKernel, clockScale, difference]

theorem law_commonClock {K : ℕ} (hK : 2 ≤ K) (k : ℝ)
    (μ : Measure (ℝ × ℝ)) : law K k k μ = FiniteSiteObservation.law K k μ := by
  rw [law_eq_semigroup hK, ← EqualRatesMutation.observationLaw_eq hK]
  rfl

theorem law_probability {K : ℕ} {a b : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμ : NonnegativeTimes μ) : IsProbabilityMeasure (law K a b μ) := by
  exact FiniteSiteObservation.law_probability hK (by norm_num) (scaled_nonnegative ha hb hμ)

theorem three_moments_eq_of_law_eq {K : ℕ} {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (heq : FiniteSiteObservation.law K k μ = FiniteSiteObservation.law K k ν) :
    firstMoment K k μ = firstMoment K k ν ∧
    secondMoment K k μ = secondMoment K k ν ∧
    jointMoment K k μ = jointMoment K k ν := by
  let i : Fin K := ⟨0, by omega⟩
  let j : Fin K := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h0 : (K : ℝ) ≠ 0 := by linarith
  have h1 : (K : ℝ)-1 ≠ 0 := by linarith
  have hdd := mass_eq_of_law_eq hK hk hμ hν heq ((i,j),(i,j))
  have hed := mass_eq_of_law_eq hK hk hμ hν heq ((i,i),(i,j))
  have hde := mass_eq_of_law_eq hK hk hμ hν heq ((i,j),(i,i))
  rw [mass_eq_moments hK hk hμ, mass_eq_moments hK hk hν] at hdd hed hde
  simp only [pattern, orientations, hij, ↓reduceIte] at hdd hed hde
  have hq := (div_left_inj' (mul_ne_zero (mul_ne_zero h0 h1)
    (mul_ne_zero h0 h1))).mp hdd
  have hpb := (div_left_inj' (mul_ne_zero h0 (mul_ne_zero h0 h1))).mp hed
  have hpa := (div_left_inj' (mul_ne_zero (mul_ne_zero h0 h1) h0)).mp hde
  exact ⟨by linarith, by linarith, hq⟩

def laplace (μ : Measure (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  ∫ t, Real.exp (-(a*t.1)) * Real.exp (-(b*t.2)) ∂μ

lemma first_exp_integrable {a : ℝ} {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (ha : 0 ≤ a) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => Real.exp (-(a*t.1))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [ht.1])

lemma second_exp_integrable {b : ℝ} {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hb : 0 ≤ b) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => Real.exp (-(b*t.2))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [ht.2])

lemma product_exp_integrable {a b : ℝ} {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => Real.exp (-(a*t.1))*Real.exp (-(b*t.2))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact (mul_le_of_le_one_left (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by nlinarith [ht.1]))).trans
      (Real.exp_le_one_iff.mpr (by nlinarith [ht.2]))

lemma scaled_firstMoment {K : ℕ} {a b : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (ha : 0 ≤ a) (hμ : NonnegativeTimes μ) :
    firstMoment K 1 (μ.map (clockScale a b)) = limit K * (1-laplace μ a 0) := by
  unfold firstMoment
  rw [integral_map (clockScale_measurable a b).aemeasurable (by
    unfold difference
    fun_prop)]
  simp only [clockScale, difference, neg_mul, one_mul, laplace, neg_zero, zero_mul,
    Real.exp_zero, mul_one]
  rw [integral_const_mul, integral_sub (integrable_const 1) (first_exp_integrable ha hμ)]
  simp

lemma scaled_secondMoment {K : ℕ} {a b : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hb : 0 ≤ b) (hμ : NonnegativeTimes μ) :
    secondMoment K 1 (μ.map (clockScale a b)) = limit K * (1-laplace μ 0 b) := by
  unfold secondMoment
  rw [integral_map (clockScale_measurable a b).aemeasurable (by
    unfold difference
    fun_prop)]
  simp only [clockScale, difference, neg_mul, one_mul, laplace, neg_zero, zero_mul,
    Real.exp_zero]
  rw [integral_const_mul, integral_sub (integrable_const 1) (second_exp_integrable hb hμ)]
  simp

lemma scaled_jointMoment {K : ℕ} {a b : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (ha : 0 ≤ a) (hb : 0 ≤ b) (hμ : NonnegativeTimes μ) :
    jointMoment K 1 (μ.map (clockScale a b)) =
      (limit K)^2 * (1-laplace μ a 0-laplace μ 0 b+laplace μ a b) := by
  unfold jointMoment
  rw [integral_map (clockScale_measurable a b).aemeasurable (by
    unfold difference
    fun_prop)]
  have hf := first_exp_integrable ha hμ
  have hg := second_exp_integrable hb hμ
  have hfg := product_exp_integrable ha hb hμ
  have h1 : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) μ := integrable_const 1
  have he : (fun t : ℝ × ℝ => difference K 1 (clockScale a b t).1 *
      difference K 1 (clockScale a b t).2) = fun t =>
      (limit K)^2 * (1-Real.exp (-(a*t.1))-Real.exp (-(b*t.2))+
        Real.exp (-(a*t.1))*Real.exp (-(b*t.2))) := by
    funext t
    simp only [difference, clockScale, neg_mul, one_mul]
    ring
  have hf1 : Integrable (fun t => 1-Real.exp (-(a*t.1))) μ := h1.sub hf
  have hf2 : Integrable (fun t => 1-Real.exp (-(a*t.1))-Real.exp (-(b*t.2))) μ := hf1.sub hg
  rw [he, integral_const_mul, integral_add hf2 hfg,
    integral_sub hf1 hg, integral_sub h1 hf]
  simp [laplace]

theorem laplace_eq_of_law_eq {K : ℕ} {a b : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (heq : law K a b μ = law K a b ν) :
    laplace μ a 0 = laplace ν a 0 ∧ laplace μ 0 b = laplace ν 0 b ∧
    laplace μ a b = laplace ν a b := by
  obtain ⟨hf,hg,hfg⟩ := three_moments_eq_of_law_eq hK (by norm_num : (0:ℝ) ≤ 1)
    (scaled_nonnegative ha hb hμ) (scaled_nonnegative ha hb hν) heq
  rw [scaled_firstMoment ha hμ, scaled_firstMoment ha hν] at hf
  rw [scaled_secondMoment hb hμ, scaled_secondMoment hb hν] at hg
  rw [scaled_jointMoment ha hb hμ, scaled_jointMoment ha hb hν] at hfg
  have hL : limit K ≠ 0 := ne_of_gt (limit_pos hK)
  have hf' := mul_left_cancel₀ hL hf
  have hg' := mul_left_cancel₀ hL hg
  have hfg' := mul_left_cancel₀ (pow_ne_zero 2 hL) hfg
  exact ⟨by linarith, by linarith, by linarith⟩

theorem law_eq_of_laplace_eq {K : ℕ} {a b : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hf : laplace μ a 0 = laplace ν a 0)
    (hg : laplace μ 0 b = laplace ν 0 b)
    (hfg : laplace μ a b = laplace ν a b) : law K a b μ = law K a b ν := by
  have hf' : firstMoment K 1 (μ.map (clockScale a b)) =
      firstMoment K 1 (ν.map (clockScale a b)) := by
    rw [scaled_firstMoment ha hμ, scaled_firstMoment ha hν, hf]
  have hg' : secondMoment K 1 (μ.map (clockScale a b)) =
      secondMoment K 1 (ν.map (clockScale a b)) := by
    rw [scaled_secondMoment hb hμ, scaled_secondMoment hb hν, hg]
  have hfg' : jointMoment K 1 (μ.map (clockScale a b)) =
      jointMoment K 1 (ν.map (clockScale a b)) := by
    rw [scaled_jointMoment ha hb hμ, scaled_jointMoment ha hb hν, hf, hg, hfg]
  have hm : mass K 1 (μ.map (clockScale a b)) = mass K 1 (ν.map (clockScale a b)) := by
    funext s
    rw [mass_eq_moments hK (by norm_num) (scaled_nonnegative ha hb hμ),
      mass_eq_moments hK (by norm_num) (scaled_nonnegative ha hb hν), hf', hg', hfg']
  simp only [law, FiniteSiteObservation.law, hm]

theorem law_eq_iff_laplace_eq {K : ℕ} {a b : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν) :
    law K a b μ = law K a b ν ↔
      laplace μ a 0 = laplace ν a 0 ∧ laplace μ 0 b = laplace ν 0 b ∧
        laplace μ a b = laplace ν a b :=
  ⟨laplace_eq_of_law_eq hK ha hb hμ hν,
    fun h => law_eq_of_laplace_eq hK ha hb hμ hν h.1 h.2.1 h.2.2⟩

theorem laplace_nat_eq_of_positive_grid {K : ℕ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (heq : ∀ m n : ℕ, law K (m+1) (n+1) μ = law K (m+1) (n+1) ν) :
    ∀ m n : ℕ, laplace μ m n = laplace ν m n := by
  intro m n
  cases m with
  | zero =>
    cases n with
    | zero => simp [laplace]
    | succ n =>
      simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
        (laplace_eq_of_law_eq hK (by positivity) (by positivity) hμ hν (heq 0 n)).2.1
  | succ m =>
    cases n with
    | zero =>
      simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
        (laplace_eq_of_law_eq hK (by positivity) (by positivity) hμ hν (heq m 0)).1
    | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        (laplace_eq_of_law_eq hK (by positivity) (by positivity) hμ hν (heq m n)).2.2

end IndependentClockObservation
end Rhone.Statistics.Identifiability
