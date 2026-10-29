/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: elimination for two linked lineages -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_h41 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z17 : Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h41 := hrec ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z10, z14, z17] at h41
  linear_combination h41

theorem unique_piece_k45 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h45 : (-4) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ + (2 * thA + thB + 6) * Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (h41 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 0, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h45 + (4) * h41

theorem unique_piece_k32 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h32 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 2, 0, 1, 0, 0,
      0, 0⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * h32 + (rhoL) * z36

theorem unique_piece_k33 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h33 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 2, 1, 0, 0, 0,
      0, 0⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * h33 + (rhoL) * z37

theorem unique_piece_k34 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h34 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0,
      0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * h34 + (rhoL) * z42

theorem unique_piece_k35 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h35 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0,
      0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h35 + (rhoL) * z43

theorem unique_piece_k38 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h38 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0,
      0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * h38 + (rhoL) * z42

theorem unique_piece_k39 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h39 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0,
      0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * h39 + (rhoL) * z43

theorem unique_piece_k40 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h40 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 0, 1, 0, 0,
      0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * h40 + (rhoL) * z44

theorem unique_piece_k41 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h41 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 0, 0, 0,
      0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + thB + rhoL) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h41 + (rhoL) * z45

theorem unique_piece_h56 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 0, 0,
      1⟩ + (-rhoL) * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h56 := hrec ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z18, z26, z32, z36] at h56
  linear_combination h56

theorem unique_piece_h46 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ + (-2 * rhoL) * Δ ⟨0, 1, 0, 1,
      0, 0, 0, 1⟩ = 0 := by
  have h46 := hrec ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z7, z18, z32] at h46
  linear_combination h46

theorem unique_piece_st56 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h56 : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 0,
      0, 1⟩ + (-rhoL) * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0)
    (h46 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ + (-2 * rhoL) * Δ ⟨0, 1,
      0, 1, 0, 0, 0, 1⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h56 + (2) * h46

theorem unique_piece_h57 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 0, 1,
      0⟩ + (-rhoL) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h57 := hrec ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z19, z27, z33, z36] at h57
  linear_combination h57

theorem unique_piece_h47 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 1, 0,
      0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0 := by
  have h47 := hrec ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z19, z22, z32, z33] at h47
  linear_combination h47

theorem unique_piece_st57 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h57 : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 0,
      1, 0⟩ + (-rhoL) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h47 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h57 + (2) * h47

theorem unique_piece_h58 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 1, 0,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h58 := hrec ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z20, z26, z34, z42] at h58
  linear_combination h58

theorem unique_piece_h49 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 1, 0,
      1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0 := by
  have h49 := hrec ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z18, z20, z34, z38] at h49
  linear_combination h49

theorem unique_piece_st58 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h58 : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 0, 1,
      0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (h49 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 0,
      1, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h58 + (2) * h49

theorem unique_piece_h59 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 1, 0, 0,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h59 := hrec ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z21, z27, z35, z42] at h59
  linear_combination h59

theorem unique_piece_h52 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 1, 1,
      0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0 := by
  have h52 := hrec ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z21, z22, z35, z38] at h52
  linear_combination h52

theorem unique_piece_st59 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h59 : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 1, 1, 0,
      0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h52 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 0,
      1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h59 + (2) * h52

end Rhone.Algebra.KilledSystem
