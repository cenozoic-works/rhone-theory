/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: elimination for states with two lineages -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_h4 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z0 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 * thB + 2) * Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h4 := hrec ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z0] at h4
  linear_combination h4

theorem unique_piece_k4 {F : Type*} [Field F] (thB : F) (Δ : St → F)
    (h4 : (2 * thB + 2) * Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thB) * Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h4

theorem unique_piece_h5 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z0 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z1 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 * thB + 2) * Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h5 := hrec ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z0, z1] at h5
  linear_combination h5

theorem unique_piece_k5 {F : Type*} [Field F] (thB : F) (Δ : St → F)
    (h5 : (2 * thB + 2) * Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thB) * Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h5

theorem unique_piece_h6 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z1 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 * thB + 2) * Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h6 := hrec ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z1] at h6
  linear_combination h6

theorem unique_piece_k6 {F : Type*} [Field F] (thB : F) (Δ : St → F)
    (h6 : (2 * thB + 2) * Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thB) * Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h6

theorem unique_piece_h11 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z0 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z2 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (thA + thB + 2) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  have h11 := hrec ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z0, z2, z7] at h11
  linear_combination h11

theorem unique_piece_k11 {F : Type*} [Field F] (thA thB : F) (Δ : St → F)
    (h11 : (thA + thB + 2) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + thB) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h11

theorem unique_piece_h12 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z1 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z2 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (thA + thB + 2) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  have h12 := hrec ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z1, z2, z8] at h12
  linear_combination h12

theorem unique_piece_k12 {F : Type*} [Field F] (thA thB : F) (Δ : St → F)
    (h12 : (thA + thB + 2) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + thB) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h12

theorem unique_piece_h13 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z0 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z3 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (thA + thB + 2) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  have h13 := hrec ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z0, z3, z9] at h13
  linear_combination h13

theorem unique_piece_k13 {F : Type*} [Field F] (thA thB : F) (Δ : St → F)
    (h13 : (thA + thB + 2) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + thB) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h13

theorem unique_piece_h14 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z1 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z3 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (thA + thB + 2) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  have h14 := hrec ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z1, z3, z10] at h14
  linear_combination h14

theorem unique_piece_k14 {F : Type*} [Field F] (thA thB : F) (Δ : St → F)
    (h14 : (thA + thB + 2) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + thB) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h14

theorem unique_piece_h15 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z2 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 * thA + 2) * Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  have h15 := hrec ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z2] at h15
  linear_combination h15

theorem unique_piece_k15 {F : Type*} [Field F] (thA : F) (Δ : St → F)
    (h15 : (2 * thA + 2) * Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA) * Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h15

theorem unique_piece_h16 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z2 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    (z3 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 * thA + 2) * Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  have h16 := hrec ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z2, z3] at h16
  linear_combination h16

theorem unique_piece_k16 {F : Type*} [Field F] (thA : F) (Δ : St → F)
    (h16 : (2 * thA + 2) * Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA) * Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h16

theorem unique_piece_h17 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z3 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 * thA + 2) * Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  have h17 := hrec ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z3] at h17
  linear_combination h17

theorem unique_piece_k17 {F : Type*} [Field F] (thA : F) (Δ : St → F)
    (h17 : (2 * thA + 2) * Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA) * Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h17

theorem unique_piece_h26 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z4 : Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ + (thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h26 := hrec ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z4, z11] at h26
  linear_combination h26

theorem unique_piece_h18 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z4 : Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩
      = 0 := by
  have h18 := hrec ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z4, z7, z11] at h18
  linear_combination h18

theorem unique_piece_k26 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h26 : (-4) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ + (thA + 2 * thB + 6) * Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (h18 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 2, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h26 + (4) * h18

theorem unique_piece_h27 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ + (-2) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ + (thA + 2 * thB + 6) *
      Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h27 := hrec ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z11, z12] at h27
  linear_combination h27

end Rhone.Algebra.KilledSystem
