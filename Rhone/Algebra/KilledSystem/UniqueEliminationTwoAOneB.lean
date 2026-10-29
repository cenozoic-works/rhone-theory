/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: elimination for two `A` and one `B` lineage -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_k24 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h24 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * h24 + (rhoL) * z30

theorem unique_piece_k25 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h25 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 2, 0, 0, 0,
      0, 0⟩ = 0)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h25 + (rhoL) * z31

theorem unique_piece_h36 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z15 : Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ + (2 * thA + thB + 6) * Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  have h36 := hrec ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z11, z15] at h36
  linear_combination h36

theorem unique_piece_h32 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z15 : Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h32 := hrec ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z7, z11, z15] at h32
  linear_combination h32

theorem unique_piece_k36 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h36 : (-4) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ + (2 * thA + thB + 6) * Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    (h32 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 2, 0, 1, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h36 + (4) * h32

theorem unique_piece_h37 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z15 : Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ + (2 * thA + thB + 6) * Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  have h37 := hrec ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z12, z15] at h37
  linear_combination h37

theorem unique_piece_h33 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z15 : Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h33 := hrec ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z8, z12, z15] at h33
  linear_combination h33

theorem unique_piece_k37 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h37 : (-4) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ + (2 * thA + thB + 6) * Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    (h33 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 2, 1, 0, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h37 + (4) * h33

theorem unique_piece_h42 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ + (-2) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ + (2 * thA + thB + 6) *
      Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  have h42 := hrec ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z11, z13, z16] at h42
  linear_combination h42

theorem unique_piece_h34 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h34 := hrec ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z9, z11, z16] at h34
  linear_combination h34

theorem unique_piece_h38 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h38 := hrec ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z7, z13, z16] at h38
  linear_combination h38

theorem unique_piece_k42 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h42 : (-2) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ + (-2) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ + (2 * thA + thB +
      6) * Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (h34 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0,
      0, 0⟩ = 0)
    (h38 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨1, 1, 0, 1, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h42 + (2) * h34 + (2) * h38

theorem unique_piece_h43 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ + (-2) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + (2 * thA + thB + 6) *
      Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  have h43 := hrec ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z12, z14, z16] at h43
  linear_combination h43

theorem unique_piece_h35 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h35 := hrec ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z10, z12, z16] at h35
  linear_combination h35

theorem unique_piece_h39 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h39 := hrec ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z8, z14, z16] at h39
  linear_combination h39

theorem unique_piece_k43 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h43 : (-2) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ + (-2) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + (2 * thA + thB +
      6) * Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (h35 : (rhoL + 2 * thA + thB + 2) * Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0,
      0, 0⟩ = 0)
    (h39 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 0, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h43 + (2) * h35 + (2) * h39

theorem unique_piece_h44 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z17 : Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ + (2 * thA + thB + 6) * Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := by
  have h44 := hrec ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z13, z17] at h44
  linear_combination h44

theorem unique_piece_h40 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z17 : Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h40 := hrec ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z9, z13, z17] at h40
  linear_combination h40

theorem unique_piece_k44 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h44 : (-4) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ + (2 * thA + thB + 6) * Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (h40 : (rhoL + 2 * thA + thB + 2) * Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 0, 1, 0, 0,
      0, 0⟩ = 0)
    : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL) * Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + 2 * thA + thB + 2) * h44 + (4) * h40

theorem unique_piece_h45 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z17 : Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ + (2 * thA + thB + 6) * Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := by
  have h45 := hrec ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z14, z17] at h45
  linear_combination h45

end Rhone.Algebra.KilledSystem
