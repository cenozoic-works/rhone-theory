/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSize
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Controlled harmonic-mean asymptotic -/

@[expose] public section

namespace Rhone.MarkovChain.EffectiveSize

open Finset Filter Topology

noncomputable def productMatchedSize {T : ℕ} (a : Fin T → ℝ) (L : ℝ) : ℝ :=
  1 / (2 * (1 - Real.rpow (∏ t, (1 - 1 / (2 * L * a t))) (1 / (T : ℝ))))

theorem tendsto_product_matched_size {T : ℕ} (hT : 0 < T)
    (a : Fin T → ℝ) (ha : ∀ t, 0 < a t) :
    Tendsto (fun L : ℕ => productMatchedSize a (L : ℝ) / (L : ℝ))
      atTop (nhds (harmonicSize a)) := by
  let P : ℝ → ℝ := fun x => ∏ t, (1 - x / (2 * a t))
  let Q : ℝ → ℝ := fun x => Real.rpow (P x) (1 / (T : ℝ))
  let A : ℝ := ∑ t, 1 / (2 * a t)
  let d : ℝ := -A * (1 / (T : ℝ))
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hA : 0 < A := by
    apply sum_pos
    · intro t _
      exact one_div_pos.mpr (mul_pos (by norm_num) (ha t))
    · exact ⟨⟨0, hT⟩, mem_univ _⟩
  have hP0 : P 0 = 1 := by simp [P]
  have hQ0 : Q 0 = 1 := by simp [Q, hP0]
  have hfac : ∀ t : Fin T, HasDerivAt (fun x : ℝ => 1 - x / (2 * a t))
      (-(1 / (2 * a t))) 0 := by
    intro t
    simpa using ((hasDerivAt_id 0).div_const (2 * a t)).const_sub (1 : ℝ)
  have hP : HasDerivAt P (-A) 0 := by
    have hp := HasDerivAt.fun_finsetProd (u := univ) (fun t _ => hfac t)
    simpa [P, A] using hp
  have hQ : HasDerivAt Q d 0 := by
    have hq := hP.rpow_const (p := 1 / (T : ℝ)) (Or.inl (by rw [hP0]; norm_num))
    simpa [Q, d, hP0] using hq
  have hd : d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hA.ne') (by positivity)
  have hslope := hQ.tendsto_slope_zero_right
  simp only [zero_add, hQ0, smul_eq_mul] at hslope
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)).div (hslope.const_mul (-2))
    (mul_ne_zero (by norm_num) hd)
  have hsum : 2 * A = ∑ t, 1 / a t := by
    unfold A
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  have hvalue : 1 / (-2 * d) = harmonicSize a := by
    unfold harmonicSize d
    rw [← hsum]
    field_simp
  rw [hvalue] at hlim
  have hx0 : Tendsto (fun L : ℕ => (1 : ℝ) / L) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hx : Tendsto (fun L : ℕ => (1 : ℝ) / L) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx0, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with L hL
    exact one_div_pos.mpr (by exact_mod_cast (show 0 < L by omega))
  have hfinal := hlim.comp hx
  apply hfinal.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL' : (L : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hPmatch : P (1 / (L : ℝ)) = ∏ t, (1 - 1 / (2 * (L : ℝ) * a t)) := by
    unfold P
    apply prod_congr rfl
    intro t _
    congr 1
    field_simp
  change 1 / (-2 * ((1 / (L : ℝ))⁻¹ * (Q (1 / (L : ℝ)) - 1))) =
    productMatchedSize a (L : ℝ) / (L : ℝ)
  unfold productMatchedSize
  rw [← hPmatch]
  change 1 / (-2 * ((1 / (L : ℝ))⁻¹ * (Q (1 / (L : ℝ)) - 1))) =
    (1 / (2 * (1 - Q (1 / (L : ℝ))))) / (L : ℝ)
  have hneg : 2 * (1 - Q (1 / (L : ℝ))) = -2 * (Q (1 / (L : ℝ)) - 1) := by ring
  rw [hneg]
  simp only [inv_inv, div_eq_mul_inv, mul_inv_rev]
  ring

end Rhone.MarkovChain.EffectiveSize
