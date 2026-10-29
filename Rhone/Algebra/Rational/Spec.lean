/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.Solve

/-! # Specialization: from the solution over a field of fractions to a numerical parameter point -/

@[expose] public section

namespace Rhone.Algebra.Rational

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {R : Type*} [CommRing R] [IsDomain R]
variable {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]
variable {F : Type*} [Field F]

omit [IsDomain R] in
theorem solvesUpTo_of_isSolution {θA θB ρ : F} {πA : Fin KA → F}
    {πB : Fin KB → F} {q : Config KA KB → F} (h : IsSolution θA θB ρ πA πB q) (N : ℕ) :
    SolvesUpTo θA θB ρ πA πB N q :=
  ⟨h.empty, h.bdryA, h.bdryB, h.bdryC, fun ξ hn _ => h.recursion ξ hn⟩

theorem exists_common_denom (Q : Config KA KB → L) (s : Finset (Config KA KB)) :
    ∃ (D : R) (P : Config KA KB → R), D ≠ 0 ∧
      ∀ ξ ∈ s, algebraMap R L (P ξ) = Q ξ * algebraMap R L D := by
  classical
  choose a b hb hab using fun ξ : Config KA KB => IsFractionRing.div_surjective (A := R) (Q ξ)
  have hb0 : ∀ ξ : Config KA KB, b ξ ≠ 0 := fun ξ =>
    mem_nonZeroDivisors_iff_ne_zero.mp (hb ξ)
  refine ⟨∏ ξ ∈ s, b ξ, fun ξ => if ξ ∈ s then a ξ * ∏ η ∈ s.erase ξ, b η else 0, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun ξ _ => hb0 ξ
  · intro ξ hξ
    have hsplit : (∏ η ∈ s, b η) = b ξ * ∏ η ∈ s.erase ξ, b η :=
      (Finset.mul_prod_erase s b hξ).symm
    have hbne : algebraMap R L (b ξ) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := L) (hb ξ)
    dsimp only
    rw [ite_eq_left hξ, hsplit, map_mul, map_mul, ← hab ξ]
    field_simp

section Clear

variable {θA θB ρ : R} {πA : Fin KA → R} {πB : Fin KB → R} {Q : Config KA KB → L}
variable {D : R} {P : Config KA KB → R} {Lv : ℕ}

omit [IsDomain R] in
theorem num_eq_of_val
    (hP : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
      algebraMap R L (P ξ) = Q ξ * algebraMap R L D)
    {ξ : Config KA KB} (hlev : ξ.nA + ξ.nB ≤ Lv) {w : R}
    (hw : Q ξ = algebraMap R L w) : P ξ = w * D := by
  have h := hP ξ hlev
  rw [hw, ← map_mul] at h
  exact IsFractionRing.injective R L h

omit [IsDomain R] in
theorem mul_denom_recursion
    (hQ : IsSolution (algebraMap R L θA) (algebraMap R L θB) (algebraMap R L ρ)
      (fun i => algebraMap R L (πA i)) (fun j => algebraMap R L (πB j)) Q)
    (hP : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
      algebraMap R L (P ξ) = Q ξ * algebraMap R L D)
    (ξ : Config KA KB) (hn : 2 ≤ ξ.n) (hlev : ξ.nA + ξ.nB ≤ Lv) :
    diag θA θB ρ ξ * P ξ = rhs θA θB ρ πA πB P ξ := by
  have hdown : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB →
      algebraMap R L D * Q η = algebraMap R L (P η) := by
    intro η h1 h2
    rw [hP η (by omega), mul_comm]
  have key : algebraMap R L (diag θA θB ρ ξ * P ξ)
      = algebraMap R L (rhs θA θB ρ πA πB P ξ) := by
    rw [map_mul, diag_map (algebraMap R L), hP ξ hlev, ← mul_assoc,
      hQ.recursion ξ hn, rhs_map (algebraMap R L)]
    rw [mul_comm (rhs _ _ _ _ _ Q ξ) (algebraMap R L D), ← rhs_smul]
    exact rhs_congr _ _ _ _ _ ξ hdown
  exact IsFractionRing.injective R L key

end Clear

noncomputable def specVal (φ : R →+* F) (Lv : ℕ) (D : R) (P : Config KA KB → R)
    (πA : Fin KA → R) (πB : Fin KB → R) : Config KA KB → F :=
  fun η => if η.nA + η.nB ≤ Lv then φ (P η) / φ D
    else Config.bdryVal (fun i => φ (πA i)) (fun j => φ (πB j)) η

omit [IsDomain R] in
theorem specVal_of_le (φ : R →+* F) {Lv : ℕ} (D : R) (P : Config KA KB → R)
    (πA : Fin KA → R) (πB : Fin KB → R) {η : Config KA KB} (h : η.nA + η.nB ≤ Lv) :
    specVal φ Lv D P πA πB η = φ (P η) / φ D := by
  simp [specVal, h]

omit [IsDomain R] in
theorem solvesUpTo_specialize {θA θB ρ : R} {πA : Fin KA → R} {πB : Fin KB → R}
    {Q : Config KA KB → L} {D : R} {P : Config KA KB → R} {Lv : ℕ} (φ : R →+* F)
    (hQ : IsSolution (algebraMap R L θA) (algebraMap R L θB) (algebraMap R L ρ)
      (fun i => algebraMap R L (πA i)) (fun j => algebraMap R L (πB j)) Q)
    (hD : φ D ≠ 0)
    (hP : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
      algebraMap R L (P ξ) = Q ξ * algebraMap R L D) :
    SolvesUpTo (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j)) Lv
      (specVal φ Lv D P πA πB) := by
  have hbdry : ∀ (ξ : Config KA KB) (w : R), Q ξ = algebraMap R L w →
      specVal φ Lv D P πA πB ξ = φ w ∨ ξ.nA + ξ.nB > Lv := by
    intro ξ w hw
    by_cases hlev : ξ.nA + ξ.nB ≤ Lv
    · refine Or.inl ?_
      rw [specVal_of_le φ D P πA πB hlev, num_eq_of_val hP hlev hw, map_mul]
      field_simp
    · exact Or.inr (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hbdry 0 1 (by rw [hQ.empty, map_one]) with h | h
    · rw [h, map_one]
    · exact absurd h (by simp)
  · intro i
    rcases hbdry (Config.eA i) (πA i) (hQ.bdryA i) with h | h
    · exact h
    · rw [specVal, ite_eq_right (by omega), Config.bdryVal_eA]
  · intro j
    rcases hbdry (Config.eB j) (πB j) (hQ.bdryB j) with h | h
    · exact h
    · rw [specVal, ite_eq_right (by omega), Config.bdryVal_eB]
  · intro i j
    rcases hbdry (Config.eC i j) (πA i * πB j) (by rw [hQ.bdryC i j, map_mul]) with h | h
    · rw [h, map_mul]
    · rw [specVal, ite_eq_right (by omega), Config.bdryVal_eC]
  · intro ξ hn hlev
    have hR := mul_denom_recursion hQ hP ξ hn hlev
    have hF : diag (φ θA) (φ θB) (φ ρ) ξ * φ (P ξ)
        = rhs (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
            (fun η => φ (P η)) ξ := by
      rw [← diag_map φ, ← map_mul, hR, rhs_map φ]
    have hcongr : rhs (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
          (specVal φ Lv D P πA πB) ξ
        = rhs (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
            (fun η => (φ D)⁻¹ * φ (P η)) ξ := by
      refine rhs_congr _ _ _ _ _ ξ fun η h1 h2 => ?_
      rw [specVal_of_le φ D P πA πB (by omega), div_eq_inv_mul]
    rw [hcongr, rhs_smul, specVal_of_le φ D P πA πB hlev]
    field_simp
    linear_combination hF

end Rhone.Algebra.Rational
