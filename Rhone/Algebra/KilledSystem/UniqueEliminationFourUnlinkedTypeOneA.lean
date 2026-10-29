/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: four unlinked lineages, type-1 `A` states -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_kw63 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st63 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (st72 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st63 + (2 * rhoL) * st72

theorem unique_piece_kw67 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st58 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (st67 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st67 + (2 * rhoL) * st58

theorem unique_piece_kw68 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st62 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st68 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st68 + (2 * rhoL) * st62

theorem unique_piece_kw69 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st69 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st69 + (2 * rhoL) * st69

theorem unique_piece_kw70 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st70 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st73 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st70 + (2 * rhoL) * st73

theorem unique_piece_kw71 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st59 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st71 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st71 + (2 * rhoL) * st59

theorem unique_piece_kw72 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st63 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (st72 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st72 + (2 * rhoL) * st63

theorem unique_piece_kw73 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st70 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st73 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st73 + (2 * rhoL) * st70

theorem unique_piece_kw74 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st74 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st74 + (2 * rhoL) * st74

theorem unique_piece_h64 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (-8) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0
      := by
  have h64 := hrec ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z26, z36] at h64
  linear_combination h64

theorem unique_piece_k64 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s256 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (h64 : (-8) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨0, 2, 0, 2, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h64 + (8) * s256

theorem unique_piece_h65 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ + (-4) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB +
      12) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h65 := hrec ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z27, z36, z37] at h65
  linear_combination h65

theorem unique_piece_k65 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s257 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (s260 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (h65 : (-4) * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ + (-4) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ + (2 * thA + 2 *
      thB + 12) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨0, 2, 1, 1, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h65 + (4) * s257 + (4) * s260

theorem unique_piece_h66 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-8) * Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0
      := by
  have h66 := hrec ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z28, z37] at h66
  linear_combination h66

theorem unique_piece_k66 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s261 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (h66 : (-8) * Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨0, 2, 2, 0, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h66 + (8) * s261

theorem unique_piece_h75 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ + (-4) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB +
      12) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h75 := hrec ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z26, z29, z42] at h75
  linear_combination h75

theorem unique_piece_k75 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s258 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (s267 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (h75 : (-4) * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ + (-4) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ + (2 * thA + 2 *
      thB + 12) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨1, 1, 0, 2, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h75 + (4) * s258 + (4) * s267

theorem unique_piece_h76 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ + (-2) * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ + (-2) * Δ ⟨1, 0, 0, 1,
      0, 0, 1, 0⟩ + (-2) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨1, 1, 1, 1, 0,
      0, 0, 0⟩ = 0 := by
  have h76 := hrec ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z27, z30, z42, z43] at h76
  linear_combination h76

end Rhone.Algebra.KilledSystem
