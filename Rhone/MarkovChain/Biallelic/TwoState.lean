/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Biallelic.Defs

/-! # Biallelic-is-PIM: every 2-state rate matrix is exactly a PIM generator -/

@[expose] public section

namespace Rhone.MarkovChain.Biallelic

open Finset

variable {F : Type*} [Field F]

def rate2 (u12 u21 : F) : Fin 2 → Fin 2 → F := ![![-u12, u12], ![u21, -u21]]

@[simp] theorem rate2_zero_zero (u12 u21 : F) : rate2 u12 u21 0 0 = -u12 := rfl
@[simp] theorem rate2_zero_one (u12 u21 : F) : rate2 u12 u21 0 1 = u12 := rfl
@[simp] theorem rate2_one_zero (u12 u21 : F) : rate2 u12 u21 1 0 = u21 := rfl
@[simp] theorem rate2_one_one (u12 u21 : F) : rate2 u12 u21 1 1 = -u21 := rfl

theorem isGenerator_rate2 (u12 u21 : F) : IsGenerator (rate2 u12 u21) := by
  intro i
  fin_cases i <;> simp [Fin.sum_univ_two]

def thetaOf (u12 u21 : F) : F := 2 * (u12 + u21)

def piOf (u12 u21 : F) : Fin 2 → F :=
  ![u21 / (u12 + u21), u12 / (u12 + u21)]

@[simp] theorem piOf_zero (u12 u21 : F) : piOf u12 u21 0 = u21 / (u12 + u21) := rfl
@[simp] theorem piOf_one (u12 u21 : F) : piOf u12 u21 1 = u12 / (u12 + u21) := rfl

theorem thetaOf_div_two (h2 : (2 : F) ≠ 0) (u12 u21 : F) :
    thetaOf u12 u21 / 2 = u12 + u21 := by
  rw [thetaOf, mul_comm, mul_div_assoc, div_self h2, mul_one]

theorem sum_piOf {u12 u21 : F} (hs : u12 + u21 ≠ 0) : ∑ i, piOf u12 u21 i = 1 := by
  rw [Fin.sum_univ_two, piOf_zero, piOf_one]
  field_simp
  ring

theorem biallelic_is_pim (h2 : (2 : F) ≠ 0) {u12 u21 : F} (hs : u12 + u21 ≠ 0) :
    IsPIM (thetaOf u12 u21) (piOf u12 u21) (rate2 u12 u21) := by
  have hhalf := thetaOf_div_two h2 u12 u21
  have e00 : pimGen (thetaOf u12 u21) (piOf u12 u21) 0 0 = -u12 := by
    rw [pimGen, hhalf, piOf_zero, ite_eq_left rfl]
    field_simp
    ring
  have e01 : pimGen (thetaOf u12 u21) (piOf u12 u21) 0 1 = u12 := by
    rw [pimGen, hhalf, piOf_one, ite_eq_right (by decide), sub_zero]
    field_simp
  have e10 : pimGen (thetaOf u12 u21) (piOf u12 u21) 1 0 = u21 := by
    rw [pimGen, hhalf, piOf_zero, ite_eq_right (by decide), sub_zero]
    field_simp
  have e11 : pimGen (thetaOf u12 u21) (piOf u12 u21) 1 1 = -u21 := by
    rw [pimGen, hhalf, piOf_one, ite_eq_left rfl]
    field_simp
    ring
  have key : ∀ i j : Fin 2, rate2 u12 u21 i j = pimGen (thetaOf u12 u21) (piOf u12 u21) i j := by
    simp only [Fin.forall_fin_two, rate2_zero_zero, rate2_zero_one, rate2_one_zero,
      rate2_one_one, e00, e01, e10, e11]
    exact ⟨⟨trivial, trivial⟩, trivial, trivial⟩
  exact funext fun i => funext fun j => key i j

theorem jump_rate2 (h2 : (2 : F) ≠ 0) {u12 u21 : F} (hs : u12 + u21 ≠ 0) :
    jump (thetaOf u12 u21) (rate2 u12 u21) = fun _ j => piOf u12 u21 j := by
  have hθ : thetaOf u12 u21 ≠ 0 := mul_ne_zero h2 hs
  rw [biallelic_is_pim h2 hs, jump_pimGen h2 hθ]

theorem wgt_jump_rate2 (h2 : (2 : F) ≠ 0) {u12 u21 : F} (hs : u12 + u21 ≠ 0) :
    wgt (piOf u12 u21) (jump (thetaOf u12 u21) (rate2 u12 u21)) = piOf u12 u21 := by
  rw [jump_rate2 h2 hs]
  exact wgt_const_rows (sum_piOf hs)

theorem theta_eq_of_isPIM (h2 : (2 : F) ≠ 0) {u12 u21 θ : F} {π : Fin 2 → F}
    (hπ : ∑ i, π i = 1) (h : IsPIM θ π (rate2 u12 u21)) : θ = 2 * (u12 + u21) := by
  have h01 : u12 = θ / 2 * π 1 := by
    have hc := congrFun (congrFun h 0) 1
    rw [rate2_zero_one, pimGen, ite_eq_right (by decide), sub_zero] at hc
    exact hc
  have h10 : u21 = θ / 2 * π 0 := by
    have hc := congrFun (congrFun h 1) 0
    rw [rate2_one_zero, pimGen, ite_eq_right (by decide), sub_zero] at hc
    exact hc
  have hsum : u12 + u21 = θ / 2 := by
    rw [h01, h10, ← mul_add, add_comm (π 1) (π 0), ← Fin.sum_univ_two π, hπ, mul_one]
  rw [hsum]
  field_simp

theorem pi_eq_of_isPIM (h2 : (2 : F) ≠ 0) {u12 u21 θ : F} {π : Fin 2 → F}
    (hs : u12 + u21 ≠ 0) (hπ : ∑ i, π i = 1) (h : IsPIM θ π (rate2 u12 u21)) :
    π = piOf u12 u21 := by
  have hθ : θ = 2 * (u12 + u21) := theta_eq_of_isPIM h2 hπ h
  have hhalf : θ / 2 = u12 + u21 := by
    rw [hθ, mul_comm, mul_div_assoc, div_self h2, mul_one]
  have h01 : u12 = (u12 + u21) * π 1 := by
    have hc := congrFun (congrFun h 0) 1
    rw [rate2_zero_one, pimGen, hhalf, ite_eq_right (by decide), sub_zero] at hc
    exact hc
  have h10 : u21 = (u12 + u21) * π 0 := by
    have hc := congrFun (congrFun h 1) 0
    rw [rate2_one_zero, pimGen, hhalf, ite_eq_right (by decide), sub_zero] at hc
    exact hc
  have key : ∀ i : Fin 2, π i = piOf u12 u21 i := by
    rw [Fin.forall_fin_two, piOf_zero, piOf_one]
    exact ⟨by rw [eq_div_iff hs, mul_comm]; exact h10.symm,
      by rw [eq_div_iff hs, mul_comm]; exact h01.symm⟩
  exact funext key

theorem theta_ne_of_missing_factor_two (h2 : (2 : F) ≠ 0) {u12 u21 : F} {π : Fin 2 → F}
    (hs : u12 + u21 ≠ 0) (hπ : ∑ i, π i = 1) : ¬ IsPIM (u12 + u21) π (rate2 u12 u21) := by
  intro h
  exact hs (by linear_combination -theta_eq_of_isPIM h2 hπ h)

theorem piOf_stationary {u12 u21 : F} (hs : u12 + u21 ≠ 0) (j : Fin 2) :
    ∑ i, piOf u12 u21 i * rate2 u12 u21 i j = 0 := by
  have key : ∀ j : Fin 2, ∑ i, piOf u12 u21 i * rate2 u12 u21 i j = 0 := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.sum_univ_two, piOf_zero, piOf_one, rate2_zero_zero, rate2_one_zero]
      field_simp
      ring
    · rw [Fin.sum_univ_two, piOf_zero, piOf_one, rate2_zero_one, rate2_one_one]
      field_simp
      ring
  exact key j

theorem eq_piOf_of_stationary {u12 u21 : F} {π : Fin 2 → F} (hs : u12 + u21 ≠ 0)
    (hπ : ∑ i, π i = 1) (h : ∀ j, ∑ i, π i * rate2 u12 u21 i j = 0) :
    π = piOf u12 u21 := by
  have h0 := h 0
  rw [Fin.sum_univ_two, rate2_zero_zero, rate2_one_zero] at h0
  rw [Fin.sum_univ_two] at hπ
  have key : ∀ i : Fin 2, π i = piOf u12 u21 i := by
    rw [Fin.forall_fin_two, piOf_zero, piOf_one]
    refine ⟨?_, ?_⟩
    · rw [eq_div_iff hs]
      linear_combination -h0 + u21 * hπ
    · rw [eq_div_iff hs]
      linear_combination h0 + u12 * hπ
  exact funext key

section Ordered

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem thetaOf_pos {u12 u21 : F} (h12 : 0 ≤ u12) (h21 : 0 ≤ u21) (hs : u12 + u21 ≠ 0) :
    0 < thetaOf u12 u21 := by
  have hpos : 0 < u12 + u21 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
  rw [thetaOf]
  linarith

theorem isProbVec_piOf {u12 u21 : F} (h12 : 0 ≤ u12) (h21 : 0 ≤ u21) (hs : u12 + u21 ≠ 0) :
    IsProbVec (piOf u12 u21) where
  nonneg i := by
    have hpos : 0 < u12 + u21 := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    have key : ∀ i : Fin 2, 0 ≤ piOf u12 u21 i := by
      rw [Fin.forall_fin_two, piOf_zero, piOf_one]
      exact ⟨div_nonneg h21 hpos.le, div_nonneg h12 hpos.le⟩
    exact key i
  sum_eq_one := sum_piOf hs

end Ordered

def rate3 : Fin 3 → Fin 3 → F := ![![-1, 1, 0], ![0, 0, 0], ![0, 2, -2]]

theorem isGenerator_rate3 : IsGenerator (rate3 (F := F)) := by
  intro i
  fin_cases i <;> simp [rate3, Fin.sum_univ_three]

theorem not_isPIM_three_state (θ : F) (π : Fin 3 → F) : ¬ IsPIM θ π (rate3 (F := F)) := by
  intro h
  have h01 : (1 : F) = θ / 2 * π 1 := by
    have hc := congrFun (congrFun h 0) 1
    rw [pimGen, ite_eq_right (by decide), sub_zero] at hc
    simpa [rate3] using hc
  have h21 : (2 : F) = θ / 2 * π 1 := by
    have hc := congrFun (congrFun h 2) 1
    rw [pimGen, ite_eq_right (by decide), sub_zero] at hc
    simpa [rate3] using hc
  exact one_ne_zero (show (1 : F) = 0 by linear_combination -(h01.trans h21.symm))

end Rhone.MarkovChain.Biallelic
