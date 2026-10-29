/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: two unlinked and one linked lineage -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_h60 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 0, 0,
      1⟩ + (-rhoL) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h60 := hrec ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z22, z27, z32, z37] at h60
  linear_combination h60

theorem unique_piece_st60 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h47 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0)
    (h60 : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 0,
      0, 1⟩ + (-rhoL) * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h60 + (2) * h47

theorem unique_piece_h61 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 0, 1,
      0⟩ + (-rhoL) * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h61 := hrec ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z23, z28, z33, z37] at h61
  linear_combination h61

theorem unique_piece_h48 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ + (-2 * rhoL) * Δ ⟨0, 1, 1, 0,
      0, 0, 1, 0⟩ = 0 := by
  have h48 := hrec ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z8, z23, z33] at h48
  linear_combination h48

theorem unique_piece_st61 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h61 : (-2) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 0,
      1, 0⟩ + (-rhoL) * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0)
    (h48 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ + (-2 * rhoL) * Δ ⟨0, 1,
      1, 0, 0, 0, 1, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h61 + (2) * h48

theorem unique_piece_h62 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 1, 0,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h62 := hrec ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z24, z27, z34, z43] at h62
  linear_combination h62

theorem unique_piece_h50 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 0,
      1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0 := by
  have h50 := hrec ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z19, z24, z34, z39] at h50
  linear_combination h50

theorem unique_piece_st62 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h62 : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 0, 1,
      0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h50 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 1,
      0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h62 + (2) * h50

theorem unique_piece_h63 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 1, 0, 0,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h63 := hrec ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z25, z28, z35, z43] at h63
  linear_combination h63

theorem unique_piece_h53 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 1,
      0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0 := by
  have h53 := hrec ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z23, z25, z35, z39] at h53
  linear_combination h53

theorem unique_piece_st63 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h63 : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨0, 1, 1, 0, 1, 0,
      0, 0⟩ + (-rhoL) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (h53 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0, 1, 1,
      0, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h63 + (2) * h53

theorem unique_piece_h67 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 0, 0,
      1⟩ + (-rhoL) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h67 := hrec ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z18, z29, z38, z42] at h67
  linear_combination h67

theorem unique_piece_st67 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h49 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (h67 : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 0,
      0, 1⟩ + (-rhoL) * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h67 + (2) * h49

theorem unique_piece_h68 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 0, 1,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h68 := hrec ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z19, z30, z39, z42] at h68
  linear_combination h68

theorem unique_piece_st68 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h50 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (h68 : (-2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 0,
      1, 0⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h68 + (2) * h50

theorem unique_piece_h69 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 1, 0,
      0⟩ + (-rhoL) * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  have h69 := hrec ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z20, z29, z40, z44] at h69
  linear_combination h69

theorem unique_piece_h51 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0, 0, 1,
      0, 1, 0, 0⟩ = 0 := by
  have h51 := hrec ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z9, z20, z40] at h51
  linear_combination h51

theorem unique_piece_st69 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h69 : (-2) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 0, 1,
      0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (h51 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0,
      0, 1, 0, 1, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 0,
      1, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h69 + (2) * h51

end Rhone.Algebra.KilledSystem
