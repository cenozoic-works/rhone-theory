/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeTipSites.Channel

/-! # Stationary single-site channel: one- and two-pair moment kernels and conditional formula -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.SingleSiteChannel

open ThreeTipSites Identifiability.EqualRatesMutation

def stationaryRoots (K : ℕ) (hK : 0 < K) : Roots K 1 where
  weight := fun _ _ => 1 / (K : ℝ)
  nonneg := fun _ _ => by positivity
  normalized := fun _ => uniform_weights_sum hK

def pairCount {K : ℕ} (x : Triple K) : ℝ :=
  (if x.1 = x.2.1 then 1 else 0) + (if x.1 = x.2.2 then 1 else 0) +
    (if x.2.1 = x.2.2 then 1 else 0)

def allEqual {K : ℕ} (x : Triple K) : ℝ :=
  if x.1 = x.2.1 ∧ x.1 = x.2.2 then 1 else 0

def firstMomentKernel (k : ℝ) (t : ℝ × ℝ) : ℝ :=
  (Real.exp (-k * t.1) + 2 * Real.exp (-k * (t.1 + t.2))) / 3

def secondMomentKernel (k : ℝ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-(k / 2) * (3 * t.1 + 2 * t.2))

lemma site_eq_star {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ) (x : Triple K) :
    site K (fun _ => 1 / (K : ℝ)) k t x =
      (1 / (K : ℝ)) * ∑ z, transition K k t.1 z x.1 *
        transition K k t.1 z x.2.1 * transition K k (t.1 + 2 * t.2) z x.2.2 := by
  unfold site
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have ht : t.1 + 2 * t.2 = t.2 + (t.1 + t.2) := by ring
  rw [ht, transition_add hK k t.2 (t.1 + t.2), Matrix.mul_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [transition_symmetric K k t.2 r z]
  ring

set_option maxHeartbeats 800000 in
lemma star_expansion {K : ℕ} (hK : 0 < K) (a b : ℝ) (x : Triple K) :
    (1 / (K : ℝ)) * ∑ z : Fin K,
      (a * (if z = x.1 then 1 else 0) + (1-a) / K) *
      (a * (if z = x.2.1 then 1 else 0) + (1-a) / K) *
      (b * (if z = x.2.2 then 1 else 0) + (1-b) / K) =
    (1 - a^2 - 2*a*b + 2*a^2*b) / (K : ℝ)^3 +
      (a^2-a^2*b) * (if x.1 = x.2.1 then 1 else 0) / (K : ℝ)^2 +
      (a*b-a^2*b) * ((if x.1 = x.2.2 then 1 else 0) +
        (if x.2.1 = x.2.2 then 1 else 0)) / (K : ℝ)^2 +
      a^2*b * allEqual x / K := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  simp only [add_mul, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold allEqual
  by_cases hab : x.1 = x.2.1 <;> by_cases hac : x.1 = x.2.2 <;>
    by_cases hbc : x.2.1 = x.2.2 <;> simp_all [eq_comm] <;> field_simp <;> ring

lemma site_expansion {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ) (x : Triple K) :
    site K (fun _ => 1 / (K : ℝ)) k t x =
    (1 - Real.exp (-k*t.1) - 2*Real.exp (-k*(t.1+t.2)) +
      2*secondMomentKernel k t) / (K : ℝ)^3 +
    (Real.exp (-k*t.1)-secondMomentKernel k t) *
      (if x.1 = x.2.1 then 1 else 0) / (K : ℝ)^2 +
    (Real.exp (-k*(t.1+t.2))-secondMomentKernel k t) *
      ((if x.1 = x.2.2 then 1 else 0) + (if x.2.1 = x.2.2 then 1 else 0)) /
      (K : ℝ)^2 + secondMomentKernel k t * allEqual x / K := by
  rw [site_eq_star hK]
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, uniform, mul_one_div]
  rw [star_expansion hK]
  have h1 : Real.exp (-(k/2)*t.1)^2 = Real.exp (-k*t.1) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(k/2)*t.1) * Real.exp (-(k/2)*(t.1+2*t.2)) =
      Real.exp (-k*(t.1+t.2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-(k/2)*t.1)^2 * Real.exp (-(k/2)*(t.1+2*t.2)) =
      secondMomentKernel k t := by
    rw [h1, ← Real.exp_add]
    unfold secondMomentKernel
    congr 1
    ring
  rw [show 2 * Real.exp (-(k/2)*t.1)^2 *
    Real.exp (-(k/2)*(t.1+2*t.2)) = 2 * secondMomentKernel k t by
      rw [mul_assoc, h3], h3, h1]
  simp only [show 2 * Real.exp (-(k / 2) * t.1) *
    Real.exp (-(k / 2) * (t.1 + 2 * t.2)) =
    2 * Real.exp (-k * (t.1 + t.2)) by rw [mul_assoc, h2], h2]

lemma allEqual_rotate {K : ℕ} (a b c : Fin K) :
    allEqual (b, c, a) = allEqual (a, b, c) := by
  have h : (b = c ∧ b = a) ↔ (a = b ∧ a = c) := by aesop
  simp only [allEqual, h]

set_option maxHeartbeats 800000 in
theorem conditional_formula {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ)
    (x : Panel K 1) :
    conditional (stationaryRoots K hK) k t x =
      (1 - 3 * firstMomentKernel k t + 2 * secondMomentKernel k t) / (K : ℝ)^3 +
      (firstMomentKernel k t - secondMomentKernel k t) * pairCount (x 0) / (K : ℝ)^2 +
      secondMomentKernel k t * allEqual (x 0) / K := by
  simp only [conditional, fixedTopology, Fin.prod_univ_one, stationaryRoots,
    Fin.sum_univ_three]
  change (1 / 3 : ℝ) *
    (site K (fun _ => 1 / (K : ℝ)) k t (x 0) +
      site K (fun _ => 1 / (K : ℝ)) k t ((x 0).2.1, (x 0).2.2, (x 0).1) +
      site K (fun _ => 1 / (K : ℝ)) k t ((x 0).2.2, (x 0).1, (x 0).2.1)) = _
  rw [site_expansion hK, site_expansion hK, site_expansion hK]
  rw [allEqual_rotate (x 0).1 (x 0).2.1 (x 0).2.2,
    allEqual_rotate (x 0).2.1 (x 0).2.2 (x 0).1,
    allEqual_rotate (x 0).1 (x 0).2.1 (x 0).2.2]
  have hca : ((x 0).2.2 = (x 0).1) ↔ ((x 0).1 = (x 0).2.2) := eq_comm
  have hba : ((x 0).2.1 = (x 0).1) ↔ ((x 0).1 = (x 0).2.1) := eq_comm
  have hcb : ((x 0).2.2 = (x 0).2.1) ↔ ((x 0).2.1 = (x 0).2.2) := eq_comm
  simp only [firstMomentKernel, pairCount, hca, hba, hcb]
  ring

lemma exp_integrable {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun t => Real.exp (-(a*t.1+b*t.2))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (add_nonneg (mul_nonneg ha ht.1) (mul_nonneg hb ht.2))

lemma firstMomentKernel_integrable {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (firstMomentKernel k) μ := by
  have h1 := exp_integrable hμ hk (le_refl (0 : ℝ))
  have h2 := exp_integrable hμ hk hk
  have e1 : (fun t : ℝ × ℝ => Real.exp (-(k*t.1+0*t.2))) =
      (fun t => Real.exp (-k*t.1)) := by funext t; congr 1; ring
  have e2 : (fun t : ℝ × ℝ => Real.exp (-(k*t.1+k*t.2))) =
      (fun t => Real.exp (-k*(t.1+t.2))) := by funext t; congr 1; ring
  rw [e1] at h1
  rw [e2] at h2
  exact (h1.add (h2.const_mul 2)).div_const 3

lemma secondMomentKernel_integrable {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (secondMomentKernel k) μ := by
  have h := exp_integrable hμ (show 0 ≤ 3*k/2 by positivity) hk
  have e : (fun t : ℝ × ℝ => Real.exp (-(3*k/2*t.1+k*t.2))) =
      secondMomentKernel k := by funext t; unfold secondMomentKernel; congr 1; ring
  rwa [e] at h

def firstMoment (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ := ∫ t, firstMomentKernel k t ∂μ

def secondMoment (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ := ∫ t, secondMomentKernel k t ∂μ

theorem mass_formula {K : ℕ} (hK : 0 < K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (hμ : NonnegativeTimes μ)
    (x : Panel K 1) :
    mass (stationaryRoots K hK) k μ x =
      (1 - 3 * firstMoment k μ + 2 * secondMoment k μ) / (K : ℝ)^3 +
      (firstMoment k μ - secondMoment k μ) * pairCount (x 0) / (K : ℝ)^2 +
      secondMoment k μ * allEqual (x 0) / K := by
  have hA := firstMomentKernel_integrable hμ hk
  have hB := secondMomentKernel_integrable hμ hk
  unfold mass
  simp_rw [conditional_formula hK]
  simp only [div_eq_mul_inv]
  rw [integral_add, integral_add]
  · simp only [integral_mul_const]
    rw [integral_add, integral_sub, integral_sub]
    · simp [firstMoment, secondMoment, integral_const_mul]
    · exact hA
    · exact hB
    · exact integrable_const 1
    · exact hA.const_mul 3
    · exact (integrable_const 1).sub (hA.const_mul 3)
    · exact hB.const_mul 2
  · exact (((integrable_const 1).sub (hA.const_mul 3)).add
      (hB.const_mul 2)).mul_const _
  · exact ((hA.sub hB).mul_const _).mul_const _
  · exact ((((integrable_const 1).sub (hA.const_mul 3)).add
      (hB.const_mul 2)).mul_const _).add (((hA.sub hB).mul_const _).mul_const _)
  · exact (hB.mul_const _).mul_const _

theorem law_eq_of_moments_eq {K : ℕ} (hK : 0 < K) {k : ℝ} (hk : 0 ≤ k)
    {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hA : firstMoment k μ = firstMoment k ν)
    (hB : secondMoment k μ = secondMoment k ν) :
    law (stationaryRoots K hK) k μ = law (stationaryRoots K hK) k ν := by
  unfold law
  congr 1
  funext x
  rw [mass_formula hK hk hμ, mass_formula hK hk hν, hA, hB]

end Rhone.Statistics.SingleSiteChannel
