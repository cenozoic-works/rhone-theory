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

/-! # Inside the parameter domain: at `θ_A = θ_B = 1` all five `ρ`-poles are real -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem natDegree_E55pospt : E55pospt.natDegree = 5 := by rw [E55pospt_eq]; compute_degree!

theorem natDegree_G55pos : G55pos.natDegree = 5 := by unfold G55pos; compute_degree!

theorem natDegree_F17 : F17.natDegree = 5 := by
  have h : (6 : ZMod 17) ≠ 0 := by decide
  unfold F17; compute_degree!

theorem E55pospt_ne_zero : E55pospt ≠ 0 := by
  intro h
  have hd := natDegree_E55pospt
  rw [h, natDegree_zero] at hd
  exact absurd hd (by norm_num)

theorem F17_no_quad (b c : ZMod 17) : ¬ (X ^ 2 + C b * X + C c ∣ F17) :=
  not_dvd_of_rem_pair (F17_div b c) (by compute_degree!) (F17_rem_ne b c)

theorem F17_irreducible : Irreducible F17 :=
  irreducible_quintic natDegree_F17 F17_no_root F17_no_quad

theorem G55pos_irreducible : Irreducible G55pos := by
  refine irreducible_of_map_of_isPrimitive (Int.castRingHom (ZMod 17)) G55pos_isPrimitive ?_ ?_
  · rw [G55pos_map17, natDegree_F17, natDegree_G55pos]
  · rw [G55pos_map17]; exact F17_irreducible

theorem E55pospt_irreducible : Irreducible E55pospt := by
  rw [E55pospt_eq_map, irreducible_C_mul_iff (by norm_num : (1000 : ℚ) ≠ 0)]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    G55pos_isPrimitive).mp G55pos_irreducible

theorem card_rootSet_E55pospt_complex : Fintype.card (E55pospt.rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree E55pospt_irreducible.separable
    (IsAlgClosed.splits _)).trans natDegree_E55pospt

theorem aeval_E55pospt (x : ℝ) : aeval x E55pospt =
    6000 * x ^ 5 + 925000 * x ^ 4 + 48728000 * x ^ 3 + 1094812000 * x ^ 2
      + 10451472000 * x + 33770880000 := by
  simp [E55pospt_eq, map_ofNat]

theorem E55pospt_five_real_roots :
    ∃ x₁ x₂ x₃ x₄ x₅ : ℝ, x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧ x₄ < x₅ ∧
      aeval x₁ E55pospt = 0 ∧ aeval x₂ E55pospt = 0 ∧ aeval x₃ E55pospt = 0 ∧
      aeval x₄ E55pospt = 0 ∧ aeval x₅ E55pospt = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => aeval x E55pospt) s :=
    fun _ => E55pospt.continuousOn_aeval
  have hv : ∀ x : ℝ, (fun x : ℝ => aeval x E55pospt) x =
      6000 * x ^ 5 + 925000 * x ^ 4 + 48728000 * x ^ 3 + 1094812000 * x ^ 2
        + 10451472000 * x + 33770880000 := aeval_E55pospt
  have n73 : (fun x : ℝ => aeval x E55pospt) (-73) < 0 := by rw [hv]; norm_num
  have p72 : 0 < (fun x : ℝ => aeval x E55pospt) (-72) := by rw [hv]; norm_num
  have p40 : 0 < (fun x : ℝ => aeval x E55pospt) (-40) := by rw [hv]; norm_num
  have n39 : (fun x : ℝ => aeval x E55pospt) (-39) < 0 := by rw [hv]; norm_num
  have n23 : (fun x : ℝ => aeval x E55pospt) (-23) < 0 := by rw [hv]; norm_num
  have p22 : 0 < (fun x : ℝ => aeval x E55pospt) (-22) := by rw [hv]; norm_num
  have p13 : 0 < (fun x : ℝ => aeval x E55pospt) (-13) := by rw [hv]; norm_num
  have n12 : (fun x : ℝ => aeval x E55pospt) (-12) < 0 := by rw [hv]; norm_num
  have n7 : (fun x : ℝ => aeval x E55pospt) (-7) < 0 := by rw [hv]; norm_num
  have p6 : 0 < (fun x : ℝ => aeval x E55pospt) (-6) := by rw [hv]; norm_num
  obtain ⟨x₁, hx₁, hr₁⟩ := intermediate_value_Ioo (by norm_num : (-73 : ℝ) ≤ -72) (hc _)
    (Set.mem_Ioo.mpr ⟨n73, p72⟩)
  obtain ⟨x₂, hx₂, hr₂⟩ := intermediate_value_Ioo' (by norm_num : (-40 : ℝ) ≤ -39) (hc _)
    (Set.mem_Ioo.mpr ⟨n39, p40⟩)
  obtain ⟨x₃, hx₃, hr₃⟩ := intermediate_value_Ioo (by norm_num : (-23 : ℝ) ≤ -22) (hc _)
    (Set.mem_Ioo.mpr ⟨n23, p22⟩)
  obtain ⟨x₄, hx₄, hr₄⟩ := intermediate_value_Ioo' (by norm_num : (-13 : ℝ) ≤ -12) (hc _)
    (Set.mem_Ioo.mpr ⟨n12, p13⟩)
  obtain ⟨x₅, hx₅, hr₅⟩ := intermediate_value_Ioo (by norm_num : (-7 : ℝ) ≤ -6) (hc _)
    (Set.mem_Ioo.mpr ⟨n7, p6⟩)
  rw [Set.mem_Ioo] at hx₁ hx₂ hx₃ hx₄ hx₅
  exact ⟨x₁, x₂, x₃, x₄, x₅, by linarith [hx₁.2, hx₂.1], by linarith [hx₂.2, hx₃.1],
    by linarith [hx₃.2, hx₄.1], by linarith [hx₄.2, hx₅.1], hr₁, hr₂, hr₃, hr₄, hr₅⟩

theorem card_rootSet_E55pospt_real : Fintype.card (E55pospt.rootSet ℝ) = 5 := by
  obtain ⟨x₁, x₂, x₃, x₄, x₅, h12, h23, h34, h45, r₁, r₂, r₃, r₄, r₅⟩ :=
    E55pospt_five_real_roots
  have hge : 5 ≤ Fintype.card (E55pospt.rootSet ℝ) := by
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
    have := le_card_rootSet (S := ℝ) E55pospt_ne_zero {x₁, x₂, x₃, x₄, x₅} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)
    omega
  have hn := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv E55pospt
  simp_rw [Set.toFinset_card] at hn
  have h5 := card_rootSet_E55pospt_complex
  omega

theorem E55pospt_conj_eq_one :
    Gal.galActionHom E55pospt ℂ
      (Gal.restrict E55pospt ℂ (Complex.conjAe.restrictScalars ℚ)) = 1 := by
  rw [← Equiv.Perm.support_eq_empty_iff, ← Finset.card_eq_zero]
  have hn := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv E55pospt
  simp_rw [Set.toFinset_card] at hn
  have h5 := card_rootSet_E55pospt_complex
  have hr := card_rootSet_E55pospt_real
  omega

end Rhone.Algebra.Galois
