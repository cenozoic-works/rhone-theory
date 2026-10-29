/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.EqualRatesMutationSemigroup

/-! # The three-tip finite-sequence channel -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.ThreeTipSites

open Identifiability.EqualRatesMutation

abbrev Triple (K : ℕ) := Fin K × (Fin K × Fin K)
abbrev Panel (K L : ℕ) := Fin L → Triple K

structure Roots (K L : ℕ) where
  weight : Fin L → Fin K → ℝ
  nonneg : ∀ s r, 0 ≤ weight s r
  normalized : ∀ s, ∑ r, weight s r = 1

def cycle (K : ℕ) : Triple K ≃ Triple K where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def orientation (K : ℕ) (q : Fin 3) : Triple K ≃ Triple K :=
  if q = 0 then Equiv.refl _ else if q = 1 then cycle K else (cycle K).symm

def site (K : ℕ) (π : Fin K → ℝ) (k : ℝ) (t : ℝ × ℝ) (x : Triple K) : ℝ :=
  ∑ r, ∑ z, π r * transition K k t.2 r z * transition K k t.1 z x.1 *
    transition K k t.1 z x.2.1 * transition K k (t.1 + t.2) r x.2.2

def fixedTopology {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (x : Panel K L) : ℝ :=
  ∏ s, site K (π.weight s) k t (orientation K q (x s))

def conditional {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (x : Panel K L) : ℝ := (1 / 3 : ℝ) * ∑ q : Fin 3, fixedTopology π k t q x

lemma site_sum {K : ℕ} (hK : 0 < K) (π : Fin K → ℝ)
    (hπ : ∑ r, π r = 1) (k : ℝ) (t : ℝ × ℝ) :
    ∑ x : Triple K, site K π k t x = 1 := by
  unfold site
  rw [Finset.sum_comm]
  have h (r : Fin K) :
      (∑ x : Triple K, ∑ z, π r * transition K k t.2 r z *
        transition K k t.1 z x.1 * transition K k t.1 z x.2.1 *
        transition K k (t.1 + t.2) r x.2.2) = π r := by
    rw [Finset.sum_comm]
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, transition_row_sum hK, mul_one]
  simp_rw [h]
  exact hπ

lemma site_nonneg {K : ℕ} (π : Fin K → ℝ) (hπ : ∀ r, 0 ≤ π r)
    {k : ℝ} (hk : 0 ≤ k) {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2)
    (x : Triple K) : 0 ≤ site K π k t x := by
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hπ r)
    (transition_nonneg K hk ht.2 r z)) (transition_nonneg K hk ht.1 z x.1))
    (transition_nonneg K hk ht.1 z x.2.1))
    (transition_nonneg K hk (add_nonneg ht.1 ht.2) r x.2.2)

lemma fixedTopology_sum {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    ∑ x : Panel K L, fixedTopology π k t q x = 1 := by
  unfold fixedTopology
  rw [← Fintype.prod_sum (fun (s : Fin L) (y : Triple K) =>
    site K (π.weight s) k t (orientation K q y))]
  have h (s : Fin L) :
      ∑ x : Triple K, site K (π.weight s) k t (orientation K q x) = 1 := by
    rw [Equiv.sum_comp (orientation K q)]
    exact site_sum hK _ (π.normalized s) k t
  simp_rw [h]
  simp

lemma conditional_sum {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    (k : ℝ) (t : ℝ × ℝ) : ∑ x : Panel K L, conditional π k t x = 1 := by
  simp only [conditional, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [fixedTopology_sum hK]

lemma conditional_nonneg {K L : ℕ} (π : Roots K L) {k : ℝ} (hk : 0 ≤ k)
    {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) (x : Panel K L) :
    0 ≤ conditional π k t x := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro q _
  exact Finset.prod_nonneg fun s _ => site_nonneg _ (π.nonneg s) hk ht _

lemma conditional_bounds {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2)
    (x : Panel K L) : 0 ≤ conditional π k t x ∧ conditional π k t x ≤ 1 := by
  refine ⟨conditional_nonneg π hk ht x, ?_⟩
  rw [← conditional_sum hK π k t]
  exact Finset.single_le_sum (fun y _ => conditional_nonneg π hk ht y) (Finset.mem_univ x)

lemma conditional_measurable {K L : ℕ} (π : Roots K L) (k : ℝ) (x : Panel K L) :
    Measurable (fun t => conditional π k t x) := by
  unfold conditional fixedTopology site transition
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

abbrev NonnegativeTimes := Identifiability.FiniteSiteObservation.NonnegativeTimes

lemma conditional_integrable {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (x : Panel K L) :
    Integrable (fun t => conditional π k t x) μ := by
  refine Integrable.of_bound (conditional_measurable π k x).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (conditional_bounds hK π hk ht x).1]
  exact (conditional_bounds hK π hk ht x).2

def mass {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure (ℝ × ℝ))
    (x : Panel K L) : ℝ := ∫ t, conditional π k t x ∂μ

def law {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    Measure (Panel K L) :=
  Measure.sum fun x => ENNReal.ofReal (mass π k μ x) • Measure.dirac x

lemma law_singleton {K L : ℕ} (π : Roots K L) (k : ℝ)
    (μ : Measure (ℝ × ℝ)) (x : Panel K L) :
    law π k μ {x} = ENNReal.ofReal (mass π k μ x) := by
  simp [law, Pi.single_apply, mul_ite]

lemma mass_nonneg {K L : ℕ} (π : Roots K L) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} (hμ : NonnegativeTimes μ) (x : Panel K L) :
    0 ≤ mass π k μ x := by
  apply integral_nonneg_of_ae
  filter_upwards [hμ] with t ht
  exact conditional_nonneg π hk ht x

lemma mass_sum {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hμ : NonnegativeTimes μ) : ∑ x : Panel K L, mass π k μ x = 1 := by
  unfold mass
  rw [← integral_finsetSum _ (fun x _ => conditional_integrable hK π hk hμ x)]
  simp_rw [conditional_sum hK π k]
  simp

theorem law_probability {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hμ : NonnegativeTimes μ) : IsProbabilityMeasure (law π k μ) := by
  constructor
  simp only [law, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mass_nonneg π hk hμ x),
    mass_sum hK π hk hμ, ENNReal.ofReal_one]

end Rhone.Statistics.ThreeTipSites
