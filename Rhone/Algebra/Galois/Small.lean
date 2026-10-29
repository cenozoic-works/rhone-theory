/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Basic
public import Rhone.Algebra.Galois.Data
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-! # `Gal(E_{m,m}) = S_m` for `m = 2` and `m = 3` at rational points -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem natDegree_E22pt : E22pt.natDegree = 2 := by rw [E22pt_eq]; compute_degree!

theorem E22pt_ne_zero : E22pt ≠ 0 := by
  intro h
  have hd := natDegree_E22pt
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem E22pt_no_real_root (z : ℝ) : aeval z E22pt ≠ 0 := by
  rw [E22pt_eq]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_neg]
  nlinarith [sq_nonneg (z + 11 / 4)]

theorem E22pt_no_rat_root (x : ℚ) : ¬ E22pt.IsRoot x := by
  rw [IsRoot, E22pt_eq]
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_neg]
  nlinarith [sq_nonneg (x + 11 / 4)]

theorem E22pt_irreducible : Irreducible E22pt :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_E22pt]; decide)
    E22pt_no_rat_root

theorem card_rootSet_E22pt_complex : Fintype.card (E22pt.rootSet ℂ) = 2 :=
  (card_rootSet_eq_natDegree E22pt_irreducible.separable
    (IsAlgClosed.splits _)).trans natDegree_E22pt

theorem card_rootSet_E22pt_real : Fintype.card (E22pt.rootSet ℝ) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  obtain ⟨z, hz⟩ := x
  exact E22pt_no_real_root z (mem_rootSet.mp hz).2

theorem galActionHom_E22pt_bijective :
    Function.Bijective (Gal.galActionHom E22pt ℂ) := by
  refine Gal.galActionHom_bijective_of_prime_degree E22pt_irreducible ?_ ?_
  · rw [natDegree_E22pt]; norm_num
  · rw [card_rootSet_E22pt_complex, card_rootSet_E22pt_real]

theorem card_gal_E22pt : Fintype.card E22pt.Gal = 2 := by
  rw [Fintype.card_of_bijective galActionHom_E22pt_bijective, Fintype.card_perm,
    card_rootSet_E22pt_complex]
  decide

theorem natDegree_E33pt : E33pt.natDegree = 3 := by rw [E33pt_eq]; compute_degree!

theorem natDegree_G33 : G33.natDegree = 3 := by unfold G33; compute_degree!

theorem natDegree_F11 : F11.natDegree = 3 := by
  have h : (-6 : ZMod 11) ≠ 0 := by decide
  unfold F11; compute_degree!

theorem E33pt_ne_zero : E33pt ≠ 0 := by
  intro h
  have hd := natDegree_E33pt
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem F11_irreducible : Irreducible F11 :=
  irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_F11]; decide)
    (fun x => F11_no_root x)

theorem G33_irreducible : Irreducible G33 := by
  refine irreducible_of_map_of_isPrimitive (Int.castRingHom (ZMod 11)) G33_isPrimitive ?_ ?_
  · rw [G33_map11, natDegree_F11, natDegree_G33]
  · rw [G33_map11]; exact F11_irreducible

theorem E33pt_irreducible : Irreducible E33pt := by
  rw [E33pt_eq_map]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    G33_isPrimitive).mp G33_irreducible

theorem card_rootSet_E33pt_complex : Fintype.card (E33pt.rootSet ℂ) = 3 :=
  (card_rootSet_eq_natDegree E33pt_irreducible.separable
    (IsAlgClosed.splits _)).trans natDegree_E33pt

theorem derivative_E33pt : derivative E33pt = -18 * X ^ 2 - 158 * X - 840 := by
  rw [E33pt_eq]
  simp [derivative_add, derivative_sub, derivative_mul, map_ofNat]
  ring

theorem derivative_E33pt_no_real_root (z : ℝ) : aeval z (derivative E33pt) ≠ 0 := by
  rw [derivative_E33pt]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_neg]
  nlinarith [sq_nonneg (z + 79 / 18)]

theorem card_rootSet_E33pt_real_le : Fintype.card (E33pt.rootSet ℝ) ≤ 1 := by
  have h0 : Fintype.card ((derivative E33pt).rootSet ℝ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz⟩ := x
    exact derivative_E33pt_no_real_root z (mem_rootSet.mp hz).2
  have h1 := card_rootSet_le_derivative (F := ℚ) E33pt
  omega

theorem E33pt_real_root : ∃ x : ℝ, aeval x E33pt = 0 := by
  have hc : ContinuousOn (fun x : ℝ => aeval x E33pt) (Set.Icc 0 1) := E33pt.continuousOn_aeval
  have hf : ∀ x : ℝ, (fun x : ℝ => aeval x E33pt) x =
      -6 * x ^ 3 - 79 * x ^ 2 - 840 * x + 833 := by
    intro x; simp [E33pt_eq, map_ofNat]
  have h0 : 0 ≤ (fun x : ℝ => aeval x E33pt) 0 := by rw [hf]; norm_num
  have h1 : (fun x : ℝ => aeval x E33pt) 1 ≤ 0 := by rw [hf]; norm_num
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
    (Set.mem_Icc.mpr ⟨h1, h0⟩)
  exact ⟨x, hx⟩

theorem card_rootSet_E33pt_real : Fintype.card (E33pt.rootSet ℝ) = 1 := by
  obtain ⟨x, hx⟩ := E33pt_real_root
  have hpos : 0 < Fintype.card (E33pt.rootSet ℝ) :=
    Fintype.card_pos_iff.mpr ⟨⟨x, (mem_rootSet_of_ne E33pt_ne_zero).mpr hx⟩⟩
  have hle := card_rootSet_E33pt_real_le
  omega

theorem galActionHom_E33pt_bijective :
    Function.Bijective (Gal.galActionHom E33pt ℂ) := by
  refine Gal.galActionHom_bijective_of_prime_degree E33pt_irreducible ?_ ?_
  · rw [natDegree_E33pt]; norm_num
  · rw [card_rootSet_E33pt_complex, card_rootSet_E33pt_real]

theorem card_gal_E33pt : Fintype.card E33pt.Gal = 6 := by
  rw [Fintype.card_of_bijective galActionHom_E33pt_bijective, Fintype.card_perm,
    card_rootSet_E33pt_complex]
  decide

end Rhone.Algebra.Galois
