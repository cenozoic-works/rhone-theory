/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: elimination for one `A` and two `B` lineages -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_h19 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h19 := hrec ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z8, z11] at h19
  linear_combination h19

theorem unique_piece_h22 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h22 := hrec ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z7, z12] at h22
  linear_combination h22

theorem unique_piece_k27 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h27 : (-2) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ + (-2) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ + (thA + 2 * thB +
      6) * Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h19 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (h22 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h27 + (2) * h19 + (2) * h22

theorem unique_piece_h28 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z6 : Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h28 := hrec ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z6, z12] at h28
  linear_combination h28

theorem unique_piece_h23 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z6 : Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h23 := hrec ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z6, z8, z12] at h23
  linear_combination h23

theorem unique_piece_k28 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h28 : (-4) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (h23 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 2, 0, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h28 + (4) * h23

theorem unique_piece_h29 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z4 : Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h29 := hrec ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z4, z13] at h29
  linear_combination h29

theorem unique_piece_h20 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z4 : Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩
      = 0 := by
  have h20 := hrec ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z4, z9, z13] at h20
  linear_combination h20

theorem unique_piece_k29 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h29 : (-4) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (h20 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 2, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h29 + (4) * h20

theorem unique_piece_h30 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ + (-2) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ + (thA + 2 * thB + 6) *
      Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h30 := hrec ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z13, z14] at h30
  linear_combination h30

theorem unique_piece_h21 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h21 := hrec ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z10, z13] at h21
  linear_combination h21

theorem unique_piece_h24 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩
      = 0 := by
  have h24 := hrec ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z5, z9, z14] at h24
  linear_combination h24

theorem unique_piece_k30 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h30 : (-2) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ + (-2) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ + (thA + 2 * thB +
      6) * Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h21 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (h24 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h30 + (2) * h21 + (2) * h24

theorem unique_piece_h31 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z6 : Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (-4) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h31 := hrec ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z6, z14] at h31
  linear_combination h31

theorem unique_piece_h25 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z6 : Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩
      = 0 := by
  have h25 := hrec ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z6, z10, z14] at h25
  linear_combination h25

theorem unique_piece_k31 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h31 : (-4) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ + (thA + 2 * thB + 6) * Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (h25 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 2, 0, 0, 0,
      0, 0⟩ = 0)
    : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL) * Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0
      := by
  linear_combination (rhoL + thA + 2 * thB + 2) * h31 + (4) * h25

theorem unique_piece_k18 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h18 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0, 2, 0, 0,
      0, 0⟩ = 0)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * h18 + (rhoL) * z26

theorem unique_piece_k19 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h19 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * h19 + (rhoL) * z27

theorem unique_piece_k20 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h20 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 2, 0, 0,
      0, 0⟩ = 0)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * h20 + (rhoL) * z29

theorem unique_piece_k21 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h21 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h21 + (rhoL) * z30

theorem unique_piece_k22 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h22 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 1, 1, 0, 0,
      0, 0⟩ = 0)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * h22 + (rhoL) * z27

theorem unique_piece_k23 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h23 : (rhoL + thA + 2 * thB + 2) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 2, 0, 0, 0,
      0, 0⟩ = 0)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : (2 + thA + 2 * thB + rhoL) * Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * h23 + (rhoL) * z28

end Rhone.Algebra.KilledSystem
