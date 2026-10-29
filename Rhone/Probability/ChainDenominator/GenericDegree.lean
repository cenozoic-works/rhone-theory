/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalChain.Degrees
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

/-! # Generic diagonal-chain degrees over ℚ[θ][ρ] -/

@[expose] public section

namespace Rhone.Probability.ChainDenominator

open Polynomial
open DiagonalChain

theorem natDegree_le_of_positive_specializations (P : (ℚ[X])[X]) (d : ℕ)
    (h : ∀ a : ℚ, 0 < a → (P.map (evalRingHom a)).natDegree ≤ d) :
    P.natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  apply eq_zero_of_infinite_isRoot
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro a ha
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h a ha) hn)
  simpa only [coeff_map, coe_evalRingHom, Set.mem_ofPred_eq, IsRoot] using hz

theorem natDegree_eq_of_positive_specializations (P : (ℚ[X])[X]) (d : ℕ)
    (h : ∀ a : ℚ, 0 < a → (P.map (evalRingHom a)).natDegree = d) :
    P.natDegree = d := by
  apply le_antisymm (natDegree_le_of_positive_specializations P d (fun a ha => (h a ha).le))
  rw [← h 1 (by norm_num)]
  exact natDegree_map_le

theorem natDegree_clearedChain_generic (k t : ℕ) (hk : 1 ≤ k) (ht : t ≤ k) :
    (clearedChain (C (X : ℚ[X])) X k t).natDegree = Nat.choose (k - 1) 2 + (t - 1) := by
  apply natDegree_eq_of_positive_specializations
  intro a ha
  have h := clearedChain_map (mapRingHom (evalRingHom a)) (C (X : ℚ[X])) X k t
  simp only [coe_mapRingHom, map_C, coe_evalRingHom, eval_X, map_X] at h
  rw [h]
  exact natDegree_clearedChain ha k hk t ht

theorem natDegree_W_generic (k : ℕ) (hk : 1 ≤ k) :
    (W k (C (X : ℚ[X])) X).natDegree = Nat.choose (k - 1) 2 := by
  simpa only [W, Nat.sub_zero, Nat.zero_sub, Nat.add_zero] using
    natDegree_clearedChain_generic k 0 hk (Nat.zero_le k)

theorem natDegree_frakE_generic (k : ℕ) :
    (frakE k (C (X : ℚ[X])) X).natDegree = Nat.choose (k + 1) 2 - 1 := by
  apply natDegree_eq_of_positive_specializations
  intro a ha
  have h := frakE_map (mapRingHom (evalRingHom a)) k (C (X : ℚ[X])) X
  simp only [coe_mapRingHom, map_C, coe_evalRingHom, eval_X, map_X] at h
  rw [h]
  exact natDegree_frakE ha k

end Rhone.Probability.ChainDenominator
