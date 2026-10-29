/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ExplicitFormula.Defs
public import Rhone.LinearAlgebra.ExplicitFormula.Pos
public import Rhone.Probability.SlotDeletion.Matrix
public import Rhone.Probability.SlotDeletion.BiallelicDenominator
public import Rhone.Analysis.RecombinationExpansion.Continuant

/-! # Block-by-block solution of DL‑1 -/

@[expose] public section

namespace Rhone.Probability.ExplicitFormula

open Finset Matrix LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear
    LinearAlgebra.SlotDeletion SlotDeletion
open Analysis.RecombinationExpansion LinearAlgebra.RecombinationExpansion

variable {F : Type*} [Field F]

theorem srcR_congr (κA γA κB γB : F) (Ψ Ψ' : ℕ → ℕ → ℕ → F) {i j s : ℕ}
    (hs : s ≤ min i j)
    (h : ∀ i' j' t', i' + j' < i + j → Ψ i' j' t' = Ψ' i' j' t') :
    srcR κA γA κB γB Ψ i j s = srcR κA γA κB γB Ψ' i j s := by
  have hsi : s ≤ i := le_trans hs (min_le_left _ _)
  have hsj : s ≤ j := le_trans hs (min_le_right _ _)
  have key : ∀ (c a b d : ℕ), (c = 0 ∨ a + b < i + j) →
      (c : F) * Ψ a b d = (c : F) * Ψ' a b d := by
    intro c a b d hc
    rcases hc with hc | hc
    · rw [hc]; simp
    · rw [h a b d hc]
  have c1 := key ((i - s) * (i - s - 1)) (i - 2) j s
    (by by_cases hi : 1 ≤ i
        · right; omega
        · left; have : i - s = 0 := by omega
          simp [this])
  have c2 := key ((i - s) * s) (i - 2) j (s - 1)
    (by by_cases hi : 1 ≤ i
        · right; omega
        · left; have : i - s = 0 := by omega
          simp [this])
  have c3 := key ((i - s) * (i + s - 1)) (i - 1) j s
    (by by_cases hi : 1 ≤ i
        · right; omega
        · left; have : i - s = 0 := by omega
          simp [this])
  have c4 := key ((j - s) * (j - s - 1)) i (j - 2) s
    (by by_cases hj : 1 ≤ j
        · right; omega
        · left; have : j - s = 0 := by omega
          simp [this])
  have c5 := key ((j - s) * s) i (j - 2) (s - 1)
    (by by_cases hj : 1 ≤ j
        · right; omega
        · left; have : j - s = 0 := by omega
          simp [this])
  have c6 := key ((j - s) * (j + s - 1)) i (j - 1) s
    (by by_cases hj : 1 ≤ j
        · right; omega
        · left; have : j - s = 0 := by omega
          simp [this])
  have hq : ∀ a b d : ℕ, (2 ≤ s → a + b < i + j) →
      (s * (s - 1) : ℕ) * Ψ a b d = ((s * (s - 1) : ℕ) : F) * Ψ' a b d := by
    intro a b d hab
    refine key _ a b d ?_
    by_cases h2 : 2 ≤ s
    · right; exact hab h2
    · left
      have : s = 0 ∨ s = 1 := by omega
      rcases this with rfl | rfl <;> simp
  have c7 := hq (i - 2) (j - 2) (s - 2) (fun h2 => by omega)
  have c8 := hq (i - 2) (j - 1) (s - 2) (fun h2 => by omega)
  have c9 := hq (i - 1) (j - 2) (s - 2) (fun h2 => by omega)
  have c10 := hq (i - 1) (j - 1) (s - 1) (fun h2 => by omega)
  unfold srcR
  linear_combination κA * c1 + 2 * κA * c2 + γA * c3 + κB * c4 + 2 * κB * c5 + γB * c6
    + κA * κB * c7 + κA * γB * c8 + γA * κB * c9 + γA * γB * c10

section Solve

variable [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Phi_block (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) {i j t : ℕ}
    (hij : 0 < i + j) (ht : t ≤ min i j) :
    Phi q πA πB i j t
      = (LinearAlgebra.Tridiag.E F i j θA θB ρ)⁻¹ *
          ∑ s ∈ Finset.range (min i j + 1),
            usmaniEntry (LinearAlgebra.Tridiag.dcoef F i j θA θB ρ)
                (LinearAlgebra.Tridiag.bcoef F i j)
                (LinearAlgebra.Tridiag.ccoef F ρ) (min i j + 1) t s
              * phiRecursionSource q πA πB i j s := by
  have hE : LinearAlgebra.Tridiag.E F i j θA θB ρ ≠ 0 :=
      (LinearAlgebra.ExplicitFormula.E_pos_all hθA hθB hρ hij).ne'
  have hc : LinearAlgebra.Tridiag.cont (LinearAlgebra.Tridiag.dcoef F i j θA θB ρ)
      (LinearAlgebra.Tridiag.bcoef F i j)
      (LinearAlgebra.Tridiag.ccoef F ρ) (min i j + 1) ≠ 0 := by
    rw [← LinearAlgebra.Tridiag.E_eq_cont]; exact hE
  have hm := T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j
  rw [T_eq_trid] at hm
  have h2 := congrFun (mulVec_usmani_eq _ _ _ hc hm) ⟨t, by omega⟩
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, usmani_apply, smul_eq_mul] at h2
  rw [h2, LinearAlgebra.Tridiag.E_eq_cont]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun s => usmaniEntry (LinearAlgebra.Tridiag.dcoef F i j θA θB ρ)
        (LinearAlgebra.Tridiag.bcoef F i j)
      (LinearAlgebra.Tridiag.ccoef F ρ) (min i j + 1) t s * phiRecursionSource q πA πB i j s)
          (min i j + 1)

theorem Phi_eq_PhiTab (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    ∀ (n i j t : ℕ), i + j ≤ n → Phi q πA πB i j t = PhiTab θA θB ρ πA πB n i j t := by
  intro n
  induction n with
  | zero =>
    intro i j t hn
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hj
    rw [Phi_zero_zero hq]
    simp [PhiTab]
  | succ n ih =>
    intro i j t hn
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [Phi_zero_zero hq]
      simp [PhiTab]
    · have hij : 0 < i + j := by omega
      rw [PhiTab, ite_eq_right h00]
      have hP : Phi q πA πB i j t = Phi q πA πB i j (min t (min i j)) := by
        rcases le_total t (min i j) with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h]; exact Phi_of_min_le q πA πB h
      rw [hP, Phi_block hθA hθB hρ hq hπA hπB hij (min_le_right _ _)]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' : s ≤ min i j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [phiRecursionSource_eq_srcR]
      congr 1
      exact srcR_congr _ _ _ _ _ _ hs'
        (fun i' j' t' hlt => ih i' j' t' (by omega))

end Solve

end Rhone.Probability.ExplicitFormula
