/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Sharpness.ChainThree

/-! # Checked denominator occurrence for the level-three diagonal chain -/

@[expose] public section

namespace Rhone.Probability.Sharpness
open Polynomial DiagonalChain Analysis.RareAlleleHierarchy RareAlleleHierarchy

theorem divisor_of_cleared_coordinate
    {R F : Type*} [CommRing R] [Field F]
    (ι : R →+* F) (hι : Function.Injective ι)
    {N D E d n : R} {v : F}
    (hN : ι N = ι D * v) (hE : E ∣ D) (hcop : IsCoprime N E)
    (hd : ι d * v = ι n) : E ∣ d := by
  have heq : d * N = D * n := by
    apply hι
    simp only [map_mul]
    rw [hN]
    calc ι d * (ι D * v) = ι D * (ι d * v) := by ring
         _ = ι D * ι n := by rw [hd]
  apply hcop.symm.dvd_of_dvd_mul_right
  rw [heq]
  exact hE.mul_right n

theorem chain_three_denominator_contains
    {K F : Type*} [Field K] [Field F]
    (j : Polynomial ℚ →+* K) (hj : Function.Injective j)
    (ι : Polynomial K →+* F) (hι : Function.Injective ι)
    (ϑ : ℕ → ℕ → F)
    (hc : IsDiagChain (ι (C (j X))) (ι X) ϑ)
    (d n : Polynomial K) (hd : ι d * ϑ 3 0 = ι n) :
    ED 3 (C (j X)) X ∣ d := by
  apply divisor_of_cleared_coordinate ι hι
    (N := W 3 (C (j X)) X) (D := frakE 3 (C (j X)) X)
    (v := ϑ 3 0) (n := n)
  · rw [W_map, frakE_map]
    exact clearedChain_eq_frakE_mul _ _ hc 3 (by norm_num) 0 (by norm_num)
  · rw [frakE_succ _ _ 2 (by norm_num)]
    exact dvd_mul_left _ _
  · have h := chain_three_isCoprime_map j hj
    change IsCoprime
      ((mapRingHom j) (W 3 (C X) X)) ((mapRingHom j) (ED 3 (C X) X)) at h
    rw [W_map, ED_map] at h
    simpa using h
  · exact hd

end Rhone.Probability.Sharpness
