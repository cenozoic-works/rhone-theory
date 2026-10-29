/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisDegreeSeven.Basic
public import Rhone.Algebra.GaloisDegreeSeven.Data
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.AbelRuffini

/-! # `Gal(E_{7,7}) = S₇` at a rational point, and no root is solvable by radicals -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem natDegree_E77pt : E77pt.natDegree = 7 := by rw [E77pt_eq]; compute_degree!

theorem natDegree_G77 : G77.natDegree = 7 := by unfold G77; compute_degree!

theorem leadingCoeff_G77 : G77.leadingCoeff = 315 := by
  rw [Polynomial.leadingCoeff, natDegree_G77, G77_coeff_fst]

theorem E77pt_ne_zero : E77pt ≠ 0 := by
  intro h
  have hd := natDegree_E77pt
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem lc_ne_zero_37 : (Int.castRingHom (ZMod 37)) G77.leadingCoeff ≠ 0 := by
  rw [leadingCoeff_G77]
  decide

theorem lc_ne_zero_11 : (Int.castRingHom (ZMod 11)) G77.leadingCoeff ≠ 0 := by
  rw [leadingCoeff_G77]
  decide

theorem F11_no_quad (b c : ZMod 11) : ¬ (X ^ 2 + C b * X + C c ∣ F11) :=
  Rhone.Algebra.Galois.not_dvd_of_rem_pair (F11_div2 b c) (by compute_degree!) (F11_rem2_ne b c)

theorem F11_no_cubic (b c d : ZMod 11) :
    ¬ (X ^ 3 + C b * X ^ 2 + C c * X + C d ∣ F11) :=
  not_dvd_of_rem_triple (F11_div3 b c d) (by compute_degree!) (F11_rem3_ne b c d)

theorem G77_no_deg_one {g : ℤ[X]} (hg : g ∣ G77) : g.natDegree ≠ 1 := by
  refine no_factor_of_map (Int.castRingHom (ZMod 37)) lc_ne_zero_37 ?_ hg
  rw [G77_map37]
  exact no_monic_dvd_one F37_no_root

theorem G77_no_deg_two {g : ℤ[X]} (hg : g ∣ G77) : g.natDegree ≠ 2 := by
  refine no_factor_of_map (Int.castRingHom (ZMod 11)) lc_ne_zero_11 ?_ hg
  rw [G77_map11]
  exact no_monic_dvd_two F11_no_quad

theorem G77_no_deg_three {g : ℤ[X]} (hg : g ∣ G77) : g.natDegree ≠ 3 := by
  refine no_factor_of_map (Int.castRingHom (ZMod 11)) lc_ne_zero_11 ?_ hg
  rw [G77_map11]
  exact no_monic_dvd_three F11_no_cubic

theorem G77_irreducible : Irreducible G77 := by
  refine irreducible_of_isPrimitive_of_no_factor G77_isPrimitive natDegree_G77
    (by norm_num) ?_
  intro g hg h1 h2
  rcases (show g.natDegree = 1 ∨ g.natDegree = 2 ∨ g.natDegree = 3 by omega) with h | h | h
  · exact G77_no_deg_one hg h
  · exact G77_no_deg_two hg h
  · exact G77_no_deg_three hg h

theorem E77pt_irreducible : Irreducible E77pt := by
  rw [E77pt_eq_map, Rhone.Algebra.Galois.irreducible_C_mul_iff (by norm_num : (-64 : ℚ) ≠ 0)]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    G77_isPrimitive).mp G77_irreducible

theorem card_rootSet_E77pt_complex : Fintype.card (E77pt.rootSet ℂ) = 7 :=
  (card_rootSet_eq_natDegree E77pt_irreducible.separable
    (IsAlgClosed.splits _)).trans natDegree_E77pt

theorem card_rootSet_E77pt_real_le : Fintype.card (E77pt.rootSet ℝ) ≤ 5 := by
  have h0 : Fintype.card
      ((derivative (derivative (derivative (derivative (derivative E77pt))))).rootSet ℝ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz⟩ := x
    exact derivative5_E77pt_no_real_root z (mem_rootSet.mp hz).2
  have h1 := card_rootSet_le_derivative (F := ℚ) E77pt
  have h2 := card_rootSet_le_derivative (F := ℚ) (derivative E77pt)
  have h3 := card_rootSet_le_derivative (F := ℚ) (derivative (derivative E77pt))
  have h4 := card_rootSet_le_derivative (F := ℚ) (derivative (derivative (derivative E77pt)))
  have h5 := card_rootSet_le_derivative (F := ℚ)
    (derivative (derivative (derivative (derivative E77pt))))
  omega

theorem E77pt_five_real_roots :
    ∃ x₁ x₂ x₃ x₄ x₅ : ℝ, x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧ x₄ < x₅ ∧
      aeval x₁ E77pt = 0 ∧ aeval x₂ E77pt = 0 ∧ aeval x₃ E77pt = 0 ∧
      aeval x₄ E77pt = 0 ∧ aeval x₅ E77pt = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => aeval x E77pt) s :=
    fun _ => E77pt.continuousOn_aeval
  obtain ⟨p25, n24⟩ := E77pt_sign0
  obtain ⟨n11, p10⟩ := E77pt_sign1
  obtain ⟨p1, n0⟩ := E77pt_sign2
  obtain ⟨n5, p6⟩ := E77pt_sign3
  obtain ⟨p8, n9⟩ := E77pt_sign4
  obtain ⟨x₁, hx₁, hr₁⟩ := intermediate_value_Ioo' (by norm_num : (-25 : ℝ) ≤ -24) (hc _)
    (Set.mem_Ioo.mpr ⟨n24, p25⟩)
  obtain ⟨x₂, hx₂, hr₂⟩ := intermediate_value_Ioo (by norm_num : (-11 : ℝ) ≤ -10) (hc _)
    (Set.mem_Ioo.mpr ⟨n11, p10⟩)
  obtain ⟨x₃, hx₃, hr₃⟩ := intermediate_value_Ioo' (by norm_num : (-1 : ℝ) ≤ 0) (hc _)
    (Set.mem_Ioo.mpr ⟨n0, p1⟩)
  obtain ⟨x₄, hx₄, hr₄⟩ := intermediate_value_Ioo (by norm_num : (5 : ℝ) ≤ 6) (hc _)
    (Set.mem_Ioo.mpr ⟨n5, p6⟩)
  obtain ⟨x₅, hx₅, hr₅⟩ := intermediate_value_Ioo' (by norm_num : (8 : ℝ) ≤ 9) (hc _)
    (Set.mem_Ioo.mpr ⟨n9, p8⟩)
  rw [Set.mem_Ioo] at hx₁ hx₂ hx₃ hx₄ hx₅
  exact ⟨x₁, x₂, x₃, x₄, x₅, by linarith [hx₁.2, hx₂.1], by linarith [hx₂.2, hx₃.1],
    by linarith [hx₃.2, hx₄.1], by linarith [hx₄.2, hx₅.1], hr₁, hr₂, hr₃, hr₄, hr₅⟩

theorem card_rootSet_E77pt_real_ge : 5 ≤ Fintype.card (E77pt.rootSet ℝ) := by
  obtain ⟨x₁, x₂, x₃, x₄, x₅, h12, h23, h34, h45, r₁, r₂, r₃, r₄, r₅⟩ :=
    E77pt_five_real_roots
  have hcard : ({x₁, x₂, x₃, x₄, x₅} : Finset ℝ).card = 5 := by
    have h13 : x₁ < x₃ := h12.trans h23
    have h14 : x₁ < x₄ := h13.trans h34
    have h15 : x₁ < x₅ := h14.trans h45
    have h24 : x₂ < x₄ := h23.trans h34
    have h25 : x₂ < x₅ := h24.trans h45
    have h35 : x₃ < x₅ := h34.trans h45
    rw [Finset.card_insert_of_notMem (by simp [h12.ne, h13.ne, h14.ne, h15.ne]),
      Finset.card_insert_of_notMem (by simp [h23.ne, h24.ne, h25.ne]),
      Finset.card_insert_of_notMem (by simp [h34.ne, h35.ne]),
      Finset.card_insert_of_notMem (by simp [h45.ne]), Finset.card_singleton]
  have := Rhone.Algebra.Galois.le_card_rootSet (S := ℝ) E77pt_ne_zero {x₁, x₂, x₃, x₄, x₅} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)
  omega

theorem card_rootSet_E77pt_real : Fintype.card (E77pt.rootSet ℝ) = 5 := by
  have h1 := card_rootSet_E77pt_real_le
  have h2 := card_rootSet_E77pt_real_ge
  omega

theorem galActionHom_E77pt_bijective :
    Function.Bijective (Gal.galActionHom E77pt ℂ) := by
  refine Gal.galActionHom_bijective_of_prime_degree E77pt_irreducible ?_ ?_
  · rw [natDegree_E77pt]; norm_num
  · rw [card_rootSet_E77pt_complex, card_rootSet_E77pt_real]

theorem card_gal_E77pt : Fintype.card E77pt.Gal = 5040 := by
  rw [Fintype.card_of_bijective galActionHom_E77pt_bijective, Fintype.card_perm,
    card_rootSet_E77pt_complex]
  decide

theorem E77pt_gal_not_isSolvable : ¬ Group.IsSolvable E77pt.Gal := by
  intro h
  refine Equiv.Perm.not_isSolvable _ ?_
    (Group.isSolvable_of_surjective galActionHom_E77pt_bijective.2)
  rw_mod_cast [Cardinal.mk_fintype, card_rootSet_E77pt_complex]
  norm_num

theorem E77pt_root_not_solvableByRad (z : ℂ) (hz : aeval z E77pt = 0) :
    z ∉ solvableByRad ℚ ℂ := by
  apply mt (isSolvable_gal_of_irreducible · E77pt_irreducible hz)
  exact E77pt_gal_not_isSolvable

end Rhone.Algebra.GaloisDegreeSeven
