/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.MutationModels
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Symmetric allele mutation with a total change probability

Source: ewens2004, sec. 3.5, p. 110; felsenstein_teg2019, sec. VII.2, eq. (VII-7). -/

@[expose] public section
namespace Rhone.Dynamics.MutationModels
open Finset

noncomputable def symmetricTransition (K : ℕ) (u : ℝ)
    (i j : Fin (K + 2)) : ℝ := if i = j then 1 - u else u / (K + 1)

noncomputable def symmetricUniform (K : ℕ) (_i : Fin (K + 2)) : ℝ := 1 / (K + 2)

/-- Source: ewens2004, eq. (12.14), p. 376, eq. (12.3), p. 373; felsenstein_teg2019, sec. VII.2, eq.
(VII-7). -/
theorem symmetric_redraw_convention (K : ℕ) (u : ℝ) (i j : Fin (K + 2)) :
    symmetricTransition K u i j =
      pimTransition (u * (K + 2) / (K + 1)) (symmetricUniform K) i j := by
  have h1 : (K:ℝ) + 1 ≠ 0 := by positivity
  have h2 : (K:ℝ) + 2 ≠ 0 := by positivity
  by_cases h : i = j <;> simp [symmetricTransition, pimTransition, symmetricUniform, h]
  · field_simp
    ring
  · field_simp

/-- Source: ewens2004, eq. (12.4), p. 373; felsenstein_teg2019, sec. VII.2, eq. (VII-7). -/
theorem symmetric_uniform_probability (K : ℕ) :
    (∀ i, 0 ≤ symmetricUniform K i) ∧ ∑ i, symmetricUniform K i = 1 := by
  constructor
  · intro i; unfold symmetricUniform; positivity
  · simp only [symmetricUniform, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_ofNat]
    field_simp

/-- Source: ewens2004, sec. 3.5, p. 110, eq. (12.4), p. 373; felsenstein_teg2019, sec. VII.2, eq.
(VII-7). -/
theorem symmetric_stationary (K : ℕ) (u : ℝ) (j : Fin (K + 2)) :
    ∑ i, symmetricUniform K i * symmetricTransition K u i j = symmetricUniform K j := by
  simp_rw [symmetric_redraw_convention]
  exact pim_stationary _ _ (symmetric_uniform_probability K).2 j

/-- Source: ewens2004, eq. (12.3)–(12.4), p. 373; felsenstein_teg2019, sec. VII.2, eq. (VII-7). -/
theorem symmetric_reversible (K : ℕ) (u : ℝ) (i j : Fin (K + 2)) :
    symmetricUniform K i * symmetricTransition K u i j =
      symmetricUniform K j * symmetricTransition K u j i := by
  rw [symmetric_redraw_convention, symmetric_redraw_convention]
  exact pim_detailed_balance_general _ _ _ _

/-- Source: ewens2004, sec. 3.5, p. 110; felsenstein_teg2019, sec. VII.2, eq. (VII-7). -/
theorem symmetric_markov (K : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∀ i j, 0 ≤ symmetricTransition K u i j) ∧
    (∀ i, ∑ j, symmetricTransition K u i j = 1) := by
  constructor
  · intro i j
    unfold symmetricTransition
    split_ifs
    · exact sub_nonneg.mpr hu1
    · exact div_nonneg hu0 (by positivity)
  · intro i
    have hsym (j : Fin (K + 2)) : symmetricTransition K u i j = symmetricTransition K u j i := by
      unfold symmetricTransition
      simp only [eq_comm]
    have h := symmetric_stationary K u i
    simp only [symmetricUniform, ← mul_sum] at h
    have hn : 1 / ((K:ℝ) + 2) ≠ 0 := by positivity
    simp_rw [hsym]
    apply (mul_left_cancel₀ hn)
    simpa using h

end Rhone.Dynamics.MutationModels
