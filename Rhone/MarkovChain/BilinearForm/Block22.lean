/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.BilinearForm.LevelFunctionSource

/-! # The block-`(2,2)` closed form, unconditionally -/

@[expose] public section

namespace Rhone.MarkovChain.BilinearForm

open Finset LinearAlgebra.Recursion Config ClosedForms Probability.Denominator

variable {K KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ θA θB ρ : F} {π : Fin K → F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem block22_closed_form' (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q ξ = qHat θA θB πA πB ξ
      + Gval θA πA ξ.mA * Gval θB πB ξ.mB * gf θA θB ρ ξ.t := by
  refine block22_closed_form hθA hθB hρ hq
    (fun mA mB => Gval θA πA mA * Gval θB πB mB) ?_ ?_ hA hB
  · intro η h1 h2 h3
    exact eq_qHat_of_min_le_one hθA hθB hρ hq η (by omega)
  · intro ζ hζA hζB
    have hsrc := source_identity (ρ := ρ) (πA := πA) (πB := πB) hθA hθB ζ
    rw [twoQ1_block22 hζA hζB] at hsrc
    linear_combination -hsrc

theorem q_block22 (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q (πA := πA) (πB := πB) hθA hθB hρ ξ
      = qHat θA θB πA πB ξ + Gval θA πA ξ.mA * Gval θB πB ξ.mB * gf θA θB ρ ξ.t :=
  block22_closed_form' hθA hθB hρ (q_isSolution hθA hθB hρ) hA hB

theorem exists_two_decomp {m : Fin K → ℕ} (hm : ∑ i, m i = 2) :
    (∃ i, m = twoSame i) ∨ ∃ i i', i ≠ i' ∧ m = twoDiff i i' := by
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ, m i ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hm]; norm_num)
  have hle : m i₀ ≤ 2 := by
    have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
    omega
  rcases (by omega : m i₀ = 2 ∨ m i₀ = 1) with h2 | h1
  · refine Or.inl ⟨i₀, funext fun k => ?_⟩
    by_cases hk : k = i₀
    · subst hk; rw [h2, twoSame_apply_self]
    · have := pair_le_sum m (Ne.symm hk)
      rw [hm] at this
      rw [twoSame_apply_of_ne hk]
      omega
  · have hsplit := sum_eq_add_erase m i₀
    rw [hm, h1] at hsplit
    obtain ⟨i₁, hmem, hi₁⟩ : ∃ i ∈ Finset.univ.erase i₀, m i ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    have hne : i₁ ≠ i₀ := (Finset.mem_erase.mp hmem).1
    have hone : m i₁ = 1 := by
      have := pair_le_sum m (Ne.symm hne)
      rw [hm] at this
      omega
    refine Or.inr ⟨i₀, i₁, Ne.symm hne, funext fun k => ?_⟩
    by_cases hk0 : k = i₀
    · subst hk0; rw [h1, twoDiff_apply_left (Ne.symm hne)]
    by_cases hk1 : k = i₁
    · subst hk1; rw [hone, twoDiff_apply_right (Ne.symm hne)]
    · have := triple_le_sum m (Ne.symm hne) (Ne.symm hk0) (Ne.symm hk1)
      rw [hm] at this
      rw [twoDiff_apply_of_ne hk0 hk1]
      omega

theorem exists_Uval_of_sum_two (hθ : 0 < θ) {m : Fin K → ℕ} (hm : ∑ i, m i = 2) :
    ∃ i₁ i₂ : Fin K, Gval θ π m = -(θ * Uval π i₁ i₂) / (θ + 1) := by
  rcases exists_two_decomp hm with ⟨i, rfl⟩ | ⟨i, i', hne, rfl⟩
  · exact ⟨i, i, G_twoSame hθ i⟩
  · exact ⟨i, i', G_twoDiff hθ hne⟩

theorem block22_kappa (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    ∃ (i₁ i₂ : Fin KA) (j₁ j₂ : Fin KB),
      q ξ = qHat θA θB πA πB ξ
        + kappa θA θB ρ ξ.t * (Uval πA i₁ i₂ * Uval πB j₁ j₂) := by
  have hE : Eblock θA θB ρ ≠ 0 := (Eblock_pos hθA hθB hρ).ne'
  obtain ⟨i₁, i₂, hGA⟩ := exists_Uval_of_sum_two (π := πA) hθA (by rw [ξ.sum_mA, hA])
  obtain ⟨j₁, j₂, hGB⟩ := exists_Uval_of_sum_two (π := πB) hθB (by rw [ξ.sum_mB, hB])
  refine ⟨i₁, i₂, j₁, j₂, ?_⟩
  rw [block22_closed_form' hθA hθB hρ hq hA hB, hGA, hGB,
    G_mul_G hθA hθB (Uval πA i₁ i₂) (Uval πB j₁ j₂),
    kappa_mul hθA hθB hE (Uval πA i₁ i₂) (Uval πB j₁ j₂)]

theorem q_block22_kappa (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    ∃ (i₁ i₂ : Fin KA) (j₁ j₂ : Fin KB),
      q (πA := πA) (πB := πB) hθA hθB hρ ξ
        = qHat θA θB πA πB ξ
          + kappa θA θB ρ ξ.t * (Uval πA i₁ i₂ * Uval πB j₁ j₂) :=
  block22_kappa hθA hθB hρ (q_isSolution hθA hθB hρ) hA hB

theorem Uval_ne_zero (hpos : ∀ i, 0 < π i) (hlt : ∀ i, π i < 1) (i₁ i₂ : Fin K) :
    Uval π i₁ i₂ ≠ 0 := by
  rcases eq_or_ne i₁ i₂ with h | h
  · subst h
    rw [Uval, ite_eq_left rfl]
    exact mul_ne_zero (hpos i₁).ne' (by linarith [hlt i₁])
  · rw [Uval, ite_eq_right h]
    exact mul_ne_zero (hpos i₁).ne' (by linarith [hpos i₂])

theorem wn_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {t : ℕ} (ht : t ≤ 2) :
    0 < wn θA θB ρ t := by
  interval_cases t
  · rw [wn]; norm_num
  · rw [wn]; linarith
  · rw [wn]
    have h1 : (0 : F) < 4 * (θA + θB + 3) * (θA + θB + 6) := by nlinarith
    have h2 : (0 : F) ≤ 2 * ρ * (θA + θB + 2) := by
      have : (0 : F) < θA + θB + 2 := by linarith
      positivity
    linarith

theorem kappa_ne_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {t : ℕ} (ht : t ≤ 2) :
    kappa θA θB ρ t ≠ 0 := by
  have hE : (0 : F) < Eblock θA θB ρ := Eblock_pos hθA hθB hρ
  have h1 : (0 : F) < θA + 1 := by linarith
  have h2 : (0 : F) < θB + 1 := by linarith
  have hw : 0 < wn θA θB ρ t := wn_pos hθA hθB hρ ht
  rw [kappa]
  have : (0 : F) < θA * θB * wn θA θB ρ t := by positivity
  have hden : (0 : F) < 2 * ((θA + 1) * (θB + 1)) * Eblock θA θB ρ := by positivity
  exact (div_pos this hden).ne'

theorem ne_qHat_of_block22 (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hAp : ∀ i, 0 < πA i) (hAl : ∀ i, πA i < 1)
    (hBp : ∀ j, 0 < πB j) (hBl : ∀ j, πB j < 1)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q ξ ≠ qHat θA θB πA πB ξ := by
  obtain ⟨i₁, i₂, j₁, j₂, hval⟩ := block22_kappa hθA hθB hρ hq hA hB
  have ht : ξ.t ≤ 2 := by have := ξ.t_le_nA; omega
  have hκ : kappa θA θB ρ ξ.t ≠ 0 := kappa_ne_zero hθA hθB hρ ht
  have hU : Uval πA i₁ i₂ * Uval πB j₁ j₂ ≠ 0 :=
    mul_ne_zero (Uval_ne_zero hAp hAl i₁ i₂) (Uval_ne_zero hBp hBl j₁ j₂)
  intro hcon
  rw [hcon] at hval
  exact (mul_ne_zero hκ hU) (by linarith [hval])

end Rhone.MarkovChain.BilinearForm
