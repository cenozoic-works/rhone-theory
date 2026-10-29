/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingFlow
public import Rhone.Statistics.Identifiability.ThreeSamplingDrift
public import Rhone.Statistics.Identifiability.IntegrableRiccati

/-! # The normalized occupancy coordinates of the arbitrary-initial-row flow -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeSampling

def normalizedX (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (3 * preRow ρ k c q t 0 + preRow ρ k c q t 1) / (3 * survival ρ k c q t)

def normalizedY (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  preRow ρ k c q t 0 / survival ρ k c q t

lemma survival_ac (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (survival ρ k c q) a b :=
  ac_finset_sum Finset.univ fun i _ => preRow_ac ρ k c q hc hq a b i

lemma survival_derivative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, HasDerivAt (survival ρ k c q)
      (-c t * (3 * preRow ρ k c q t 0 + preRow ρ k c q t 1)) t := by
  filter_upwards [preRow_derivative_ae ρ k c q hc hq] with t ht
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)).congr_deriv
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
      MarkovChain.Identifiability.totalMigration]
  ring

lemma normalized_coordinates_bounds (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) :
    (0 ≤ normalizedX ρ k c q t ∧ normalizedX ρ k c q t ≤ 1) ∧
    (normalizedY ρ k c q t ≤ 1 ∧
      3 * normalizedX ρ k c q t ≤ 1 + 2 * normalizedY ρ k c q t) := by
  have hS := survival_positive ρ k c q hρ hρsum hc hq hqn ht
  have ha := preRow_nonnegative ρ k c q hρ hc hq hqn ht 0
  have hb := preRow_nonnegative ρ k c q hρ hc hq hqn ht 1
  have hd := preRow_nonnegative ρ k c q hρ hc hq hqn ht 2
  have hsum : survival ρ k c q t =
      preRow ρ k c q t 0 + preRow ρ k c q t 1 + preRow ρ k c q t 2 := by
    simp [survival, Fin.sum_univ_succ]
    ring
  have hxS : 3 * normalizedX ρ k c q t * survival ρ k c q t =
      3 * preRow ρ k c q t 0 + preRow ρ k c q t 1 := by
    unfold normalizedX
    field_simp
  have hyS : normalizedY ρ k c q t * survival ρ k c q t = preRow ρ k c q t 0 := by
    exact div_mul_cancel₀ _ hS.ne'
  refine ⟨⟨div_nonneg (by positivity) (by positivity), ?_⟩, ?_, ?_⟩
  · apply (div_le_one (mul_pos (by norm_num) hS)).mpr
    linarith
  · apply (div_le_one hS).mpr
    linarith
  · apply (mul_le_mul_iff_left₀ hS).mp
    nlinarith only [hxS, hyS, hsum, hd]

lemma normalized_coordinates_ac (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (normalizedX ρ k c q) a b ∧
    AbsolutelyContinuousOnInterval (normalizedY ρ k c q) a b := by
  have hSac := survival_ac ρ k c q hc hq a b
  obtain ⟨u, hu, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hSac.continuousOn
  have hu0 : 0 ≤ u := ha.trans (uIcc_of_le hab ▸ hu).1
  have hpos := survival_positive ρ k c q hρ hρsum hc hq hqn hu0
  have hi := ac_inv_of_positive_lower_bound hSac hpos hmin
  have h0 := preRow_ac ρ k c q hc hq a b 0
  have h1 := preRow_ac ρ k c q hc hq a b 1
  constructor
  · have h := (((h0.const_mul 3).add h1).fun_mul hi).const_mul (1 / 3 : ℝ)
    convert! h using 1
    funext t
    change (3 * preRow ρ k c q t 0 + preRow ρ k c q t 1) /
      (3 * survival ρ k c q t) =
      (1 / 3 : ℝ) * ((3 * preRow ρ k c q t 0 + preRow ρ k c q t 1) *
        (survival ρ k c q t)⁻¹)
    ring
  · change AbsolutelyContinuousOnInterval
      (fun t => preRow ρ k c q t 0 / survival ρ k c q t) a b
    simpa only [div_eq_mul_inv] using h0.fun_mul hi

end Rhone.Statistics.Identifiability.ThreeSampling
