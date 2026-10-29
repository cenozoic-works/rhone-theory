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
public import Mathlib.FieldTheory.AbelRuffini

/-! # `Gal(E_{5,5}) = S₅` at a rational point, and no root is solvable by radicals -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem natDegree_E55pt : E55pt.natDegree = 5 := by rw [E55pt_eq]; compute_degree!

theorem natDegree_G55 : G55.natDegree = 5 := by unfold G55; compute_degree!

theorem natDegree_F7 : F7.natDegree = 5 := by
  have h : (-3 : ZMod 7) ≠ 0 := by decide
  unfold F7; compute_degree!

theorem E55pt_ne_zero : E55pt ≠ 0 := by
  intro h
  have hd := natDegree_E55pt
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem F7_no_quad (b c : ZMod 7) : ¬ (X ^ 2 + C b * X + C c ∣ F7) :=
  not_dvd_of_rem_pair (F7_div b c) (by compute_degree!) (F7_rem_ne b c)

theorem F7_irreducible : Irreducible F7 :=
  irreducible_quintic natDegree_F7 F7_no_root F7_no_quad

theorem G55_irreducible : Irreducible G55 := by
  refine irreducible_of_map_of_isPrimitive (Int.castRingHom (ZMod 7)) G55_isPrimitive ?_ ?_
  · rw [G55_map7, natDegree_F7, natDegree_G55]
  · rw [G55_map7]; exact F7_irreducible

theorem E55pt_irreducible : Irreducible E55pt := by
  rw [E55pt_eq_map]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    G55_isPrimitive).mp G55_irreducible

theorem card_rootSet_E55pt_complex : Fintype.card (E55pt.rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree E55pt_irreducible.separable
    (IsAlgClosed.splits _)).trans natDegree_E55pt

theorem derivative3_E55pt :
    derivative (derivative (derivative E55pt)) = -21600 * X ^ 2 - 286416 * X - 1368918 := by
  rw [E55pt_eq]
  simp [derivative_add, derivative_sub, derivative_mul, map_ofNat]
  ring

theorem derivative3_E55pt_no_real_root (z : ℝ) :
    aeval z (derivative (derivative (derivative E55pt))) ≠ 0 := by
  rw [derivative3_E55pt]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_neg]
  nlinarith [sq_nonneg (z + 663 / 100)]

theorem card_rootSet_E55pt_real_le : Fintype.card (E55pt.rootSet ℝ) ≤ 3 := by
  have h0 : Fintype.card ((derivative (derivative (derivative E55pt))).rootSet ℝ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz⟩ := x
    exact derivative3_E55pt_no_real_root z (mem_rootSet.mp hz).2
  have h1 := card_rootSet_le_derivative (F := ℚ) E55pt
  have h2 := card_rootSet_le_derivative (F := ℚ) (derivative E55pt)
  have h3 := card_rootSet_le_derivative (F := ℚ) (derivative (derivative E55pt))
  omega

theorem E55pt_two_real_roots :
    ∃ x y : ℝ, x ≠ y ∧ aeval x E55pt = 0 ∧ aeval y E55pt = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => aeval x E55pt) s :=
    fun _ => E55pt.continuousOn_aeval
  have hf : ∀ x : ℝ, (fun x : ℝ => aeval x E55pt) x =
      -360 * x ^ 5 - 11934 * x ^ 4 - 228153 * x ^ 3 - 302673 * x ^ 2 + 9983181 * x
        - 5297981 := by
    intro x; simp [E55pt_eq, map_ofNat]
  have h0 : (fun x : ℝ => aeval x E55pt) 0 ≤ 0 := by rw [hf]; norm_num
  have h1 : 0 < (fun x : ℝ => aeval x E55pt) 1 := by rw [hf]; norm_num
  have h5 : (fun x : ℝ => aeval x E55pt) 5 ≤ 0 := by rw [hf]; norm_num
  obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico (by norm_num : (0 : ℝ) ≤ 1) (hc _)
    (Set.mem_Ico.mpr ⟨h0, h1⟩)
  obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc' (by norm_num : (1 : ℝ) ≤ 5) (hc _)
    (Set.mem_Ico.mpr ⟨h5, h1⟩)
  exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩

theorem card_rootSet_E55pt_real_ge : 2 ≤ Fintype.card (E55pt.rootSet ℝ) := by
  obtain ⟨x, y, hxy, hx, hy⟩ := E55pt_two_real_roots
  have key : ↑({x, y} : Finset ℝ) ⊆ E55pt.rootSet ℝ := by
    simp [Set.insert_subset, mem_rootSet_of_ne E55pt_ne_zero, hx, hy]
  convert! Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
    Finset.card_insert_of_notMem (mt Finset.mem_singleton.mp hxy)]

theorem card_rootSet_E55pt_real : Fintype.card (E55pt.rootSet ℝ) = 3 := by
  have hn : 2 ∣ (Gal.galActionHom E55pt ℂ
      (Gal.restrict E55pt ℂ (Complex.conjAe.restrictScalars ℚ))).support.card :=
    Equiv.Perm.two_dvd_card_support (by
      rw [← map_pow, ← map_pow,
        show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from
          AlgEquiv.ext Complex.conj_conj, map_one, map_one])
  have key := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv E55pt
  simp_rw [Set.toFinset_card] at key
  have h1 := card_rootSet_E55pt_real_le
  have h2 := card_rootSet_E55pt_real_ge
  have h3 := card_rootSet_E55pt_complex
  omega

theorem galActionHom_E55pt_bijective :
    Function.Bijective (Gal.galActionHom E55pt ℂ) := by
  refine Gal.galActionHom_bijective_of_prime_degree E55pt_irreducible ?_ ?_
  · rw [natDegree_E55pt]; norm_num
  · rw [card_rootSet_E55pt_complex, card_rootSet_E55pt_real]

theorem card_gal_E55pt : Fintype.card E55pt.Gal = 120 := by
  rw [Fintype.card_of_bijective galActionHom_E55pt_bijective, Fintype.card_perm,
    card_rootSet_E55pt_complex]
  decide

theorem E55pt_gal_not_isSolvable : ¬ Group.IsSolvable E55pt.Gal := by
  intro h
  refine Equiv.Perm.not_isSolvable _ (le_of_eq ?_)
    (Group.isSolvable_of_surjective galActionHom_E55pt_bijective.2)
  rw_mod_cast [Cardinal.mk_fintype, card_rootSet_E55pt_complex]

theorem E55pt_root_not_solvableByRad (z : ℂ) (hz : aeval z E55pt = 0) :
    z ∉ solvableByRad ℚ ℂ := by
  apply mt (isSolvable_gal_of_irreducible · E55pt_irreducible hz)
  exact E55pt_gal_not_isSolvable

end Rhone.Algebra.Galois
