/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: four unlinked lineages, type-0 `A` states -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_k76 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s259 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (s262 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (s268 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (s271 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (h76 : (-2) * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ + (-2) * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ + (-2) * Δ ⟨1, 0,
      0, 1, 0, 0, 1, 0⟩ + (-2) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨1, 1, 1,
      1, 0, 0, 0, 0⟩ = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨1, 1, 1, 1, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h76 + (2) * s259 + (2) * s262 + (2) * s268 + (2) * s271

theorem unique_piece_h77 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ + (-4) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ + (2 * thA + 2 * thB +
      12) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h77 := hrec ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z28, z31, z43] at h77
  linear_combination h77

theorem unique_piece_k77 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s263 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (s272 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (h77 : (-4) * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ + (-4) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ + (2 * thA + 2 *
      thB + 12) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨1, 1, 2, 0, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h77 + (4) * s263 + (4) * s272

theorem unique_piece_h78 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (-8) * Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0
      := by
  have h78 := hrec ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z29, z44] at h78
  linear_combination h78

theorem unique_piece_k78 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s269 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (h78 : (-8) * Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨2, 0, 0, 2, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h78 + (8) * s269

theorem unique_piece_h79 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ + (-4) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ + (2 * thA + 2 * thB +
      12) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h79 := hrec ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z30, z44, z45] at h79
  linear_combination h79

theorem unique_piece_k79 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s270 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (s273 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (h79 : (-4) * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ + (-4) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ + (2 * thA + 2 *
      thB + 12) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨2, 0, 1, 1, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h79 + (4) * s270 + (4) * s273

theorem unique_piece_h80 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-8) * Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0
      := by
  have h80 := hrec ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z31, z45] at h80
  linear_combination h80

theorem unique_piece_k80 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s274 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (h80 : (-8) * Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ + (2 * thA + 2 * thB + 12) * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = 0)
    : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 *
      rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * Δ ⟨2, 0, 2, 0, 0, 0, 0,
      0⟩ = 0 := by
  linear_combination (-4 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * h80 + (8) * s274

theorem unique_piece_k56 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s256 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (z64 : Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * s256 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z64

theorem unique_piece_k57 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s257 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z65 : Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * s257 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z65

theorem unique_piece_k58 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s258 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (z75 : Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * s258 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z75

theorem unique_piece_k59 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s259 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z76 : Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0,
      1, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * s259 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z76

theorem unique_piece_k60 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s260 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z65 : Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * s260 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z65

theorem unique_piece_k61 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s261 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (z66 : Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * s261 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z66

theorem unique_piece_k62 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s262 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z76 : Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * s262 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z76

theorem unique_piece_k63 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s263 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0,
      1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (z77 : Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1,
      0, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * s263 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z77

theorem unique_piece_k67 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s267 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (z75 : Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * s267 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z75

theorem unique_piece_k68 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s268 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z76 : Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * s268 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z76

theorem unique_piece_k69 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s269 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = 0)
    (z78 : Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * s269 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z78

end Rhone.Algebra.KilledSystem
