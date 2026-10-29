/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: combined elimination for linked states -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_h70 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 1, 0, 0,
      0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h70 := hrec ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z21, z30, z41, z44] at h70
  linear_combination h70

theorem unique_piece_h54 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 1,
      0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0 := by
  have h54 := hrec ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z21, z24, z40, z41] at h54
  linear_combination h54

theorem unique_piece_st70 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h70 : (-2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 0, 1, 1, 0,
      0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (h54 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 0,
      1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h70 + (2) * h54

theorem unique_piece_h71 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 0, 0,
      1⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h71 := hrec ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z22, z30, z38, z43] at h71
  linear_combination h71

theorem unique_piece_st71 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h52 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (h71 : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 0,
      0, 1⟩ + (-rhoL) * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h71 + (2) * h52

theorem unique_piece_h72 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 0, 1,
      0⟩ + (-rhoL) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h72 := hrec ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z23, z31, z39, z43] at h72
  linear_combination h72

theorem unique_piece_st72 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h53 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (h72 : (-2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 0,
      1, 0⟩ + (-rhoL) * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h72 + (2) * h53

theorem unique_piece_h73 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 1, 0,
      0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  have h73 := hrec ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z24, z30, z40, z45] at h73
  linear_combination h73

theorem unique_piece_st73 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h54 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (h73 : (-2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 0, 1,
      0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h73 + (2) * h54

theorem unique_piece_h74 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (-2) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 1, 0, 0,
      0⟩ + (-rhoL) * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h74 := hrec ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z25, z31, z41, z45] at h74
  linear_combination h74

theorem unique_piece_h55 {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0, 1, 0,
      1, 0, 0, 0⟩ = 0 := by
  have h55 := hrec ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ (by decide)
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, mul_zero, zero_mul,
    add_zero, zero_add, z10, z25, z41] at h55
  linear_combination h55

theorem unique_piece_st74 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h74 : (-2) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ + (rhoL + 2 * thA + 2 * thB + 6) * Δ ⟨1, 0, 1, 0, 1, 0,
      0, 0⟩ + (-rhoL) * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (h55 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0,
      1, 0, 1, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1, 0, 1,
      0, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) *
      rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  linear_combination (2 * rhoL + 2 * thA + 2 * thB + 2) * h74 + (2) * h55

theorem unique_piece_kw56 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st56 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st56 + (2 * rhoL) * st56

theorem unique_piece_kw57 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st57 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st60 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st57 + (2 * rhoL) * st60

theorem unique_piece_kw58 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st58 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (st67 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st58 + (2 * rhoL) * st67

theorem unique_piece_kw59 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st59 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 1, 0, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st71 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st59 + (2 * rhoL) * st71

theorem unique_piece_kw60 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st57 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 0, 1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st60 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 0, 1⟩ - 2 * rhoL * Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st60 + (2 * rhoL) * st57

theorem unique_piece_kw61 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st61 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st61 + (2 * rhoL) * st61

theorem unique_piece_kw62 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (st62 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨0,
      1, 1, 0, 0, 1, 0, 0⟩ - 2 * rhoL * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (st68 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 2 * rhoL) * Δ ⟨1,
      0, 0, 1, 0, 0, 1, 0⟩ - 2 * rhoL * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 *
      rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL)) * (((6 + 2 * thA + 2 *
      thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ - (2
      + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩) = 0 := by
  linear_combination (-2 * rhoL + (rhoL + 2 * thA + 2 * thB + 6) * (2 * rhoL + 2 * thA + 2 * thB +
    2)) * st62 + (2 * rhoL) * st68

end Rhone.Algebra.KilledSystem
