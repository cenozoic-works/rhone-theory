/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive

/-! # `E_{i,j} > 0` at every non-empty block -/

@[expose] public section

namespace Rhone.LinearAlgebra.ExplicitFormula

open Tridiag GaloisDegreeSeven

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem rowSum_min_pos_all {i j : ℕ} {θA θB : F} (hij : 0 < i + j)
    (hA : 0 < θA) (hB : 0 < θB) : (0 : F) < rowSum F i j θA θB (min i j) := by
  have h0 : upRate F i j (min i j) = 0 := upRate_min i j
  have hn : (0 : F) ≤ (((i + j - min i j) * (i + j - min i j - 1) : ℕ) : F) :=
    Nat.cast_nonneg _
  have h1 : (0 : F) ≤ θA * i := mul_nonneg hA.le (Nat.cast_nonneg i)
  have h2 : (0 : F) ≤ θB * j := mul_nonneg hB.le (Nat.cast_nonneg j)
  have h3 : (0 : F) < θA * i + θB * j := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · have hj : 0 < j := by omega
      have : (0 : F) < θB * j := mul_pos hB (Nat.cast_pos.mpr hj)
      linarith
    · have : (0 : F) < θA * i := mul_pos hA (Nat.cast_pos.mpr hi)
      linarith
  unfold rowSum
  rw [h0]
  linarith

theorem E_pos_all {i j : ℕ} {θA θB ρ : F} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hij : 0 < i + j) : 0 < E F i j θA θB ρ := by
  obtain ⟨hpos, hstep⟩ := cont_invariant (i := i) (j := j) hθA.le hθB.le hρ (min i j) le_rfl
  have hup : upRate F i j (min i j) = 0 := upRate_min i j
  have hrow : (0 : F) < rowSum F i j θA θB (min i j) := rowSum_min_pos_all hij hθA hθB
  rw [E_eq_cont]
  have : (0 : F) < (upRate F i j (min i j) + rowSum F i j θA θB (min i j)) *
      cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (min i j) :=
    mul_pos (by rw [hup]; linarith) hpos
  linarith

end Rhone.LinearAlgebra.ExplicitFormula
