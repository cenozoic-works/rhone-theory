/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Data

/-! # `Wval` solves the system: the 73 recursion identities and the 8 boundary conditions -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.BlockTwoSymbolic

open KilledSystem

variable {R : Type*} [CommRing R]

theorem recW_4 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_0, W0, Wval_4, W4]
  ring

theorem recW_5 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_0, W0, Wval_1, W1, Wval_5, W5]
  ring

theorem recW_6 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_1, W1, Wval_6, W6]
  ring

theorem recW_11 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_0, W0, Wval_2, W2, Wval_7, W7, Wval_11, W11]
  ring

theorem recW_12 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_1, W1, Wval_2, W2, Wval_8, W8, Wval_12, W12]
  ring

theorem recW_13 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_0, W0, Wval_3, W3, Wval_9, W9, Wval_13, W13]
  ring

theorem recW_14 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_1, W1, Wval_3, W3, Wval_10, W10, Wval_14, W14]
  ring

theorem recW_15 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 0, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_2, W2, Wval_15, W15]
  ring

theorem recW_16 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_2, W2, Wval_3, W3, Wval_16, W16]
  ring

theorem recW_17 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 0, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_3, W3, Wval_17, W17]
  ring

theorem recW_18 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ * Wval u v a b r ⟨0, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_4, W4, Wval_7, W7, Wval_11, W11, Wval_18, W18, Wval_26, W26]
  ring

theorem recW_19 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ * Wval u v a b r ⟨0, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_8, W8, Wval_11, W11, Wval_19, W19, Wval_27, W27]
  ring

theorem recW_20 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_4, W4, Wval_9, W9, Wval_13, W13, Wval_20, W20, Wval_29, W29]
  ring

theorem recW_21 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_10, W10, Wval_13, W13, Wval_21, W21, Wval_30, W30]
  ring

theorem recW_22 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ * Wval u v a b r ⟨0, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_7, W7, Wval_12, W12, Wval_22, W22, Wval_27, W27]
  ring

theorem recW_23 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ * Wval u v a b r ⟨0, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_6, W6, Wval_8, W8, Wval_12, W12, Wval_23, W23, Wval_28, W28]
  ring

theorem recW_24 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ * Wval u v a b r ⟨0, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_9, W9, Wval_14, W14, Wval_24, W24, Wval_30, W30]
  ring

theorem recW_25 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_6, W6, Wval_10, W10, Wval_14, W14, Wval_25, W25, Wval_31, W31]
  ring

theorem recW_26 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_4, W4, Wval_11, W11, Wval_18, W18, Wval_26, W26]
  ring

theorem recW_27 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_11, W11, Wval_12, W12, Wval_19, W19, Wval_22, W22, Wval_27, W27]
  ring

theorem recW_28 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_6, W6, Wval_12, W12, Wval_23, W23, Wval_28, W28]
  ring

theorem recW_29 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_4, W4, Wval_13, W13, Wval_20, W20, Wval_29, W29]
  ring

theorem recW_30 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_5, W5, Wval_13, W13, Wval_14, W14, Wval_21, W21, Wval_24, W24, Wval_30, W30]
  ring

theorem recW_31 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_6, W6, Wval_14, W14, Wval_25, W25, Wval_31, W31]
  ring

theorem recW_32 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ * Wval u v a b r ⟨0, 1, 0, 0, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_7, W7, Wval_11, W11, Wval_15, W15, Wval_32, W32, Wval_36, W36]
  ring

theorem recW_33 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ * Wval u v a b r ⟨0, 1, 0, 0, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_8, W8, Wval_12, W12, Wval_15, W15, Wval_33, W33, Wval_37, W37]
  ring

theorem recW_34 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 0, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_9, W9, Wval_11, W11, Wval_16, W16, Wval_34, W34, Wval_42, W42]
  ring

theorem recW_35 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 0, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_10, W10, Wval_12, W12, Wval_16, W16, Wval_35, W35, Wval_43, W43]
  ring

theorem recW_36 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 0, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_11, W11, Wval_15, W15, Wval_32, W32, Wval_36, W36]
  ring

theorem recW_37 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 1, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_12, W12, Wval_15, W15, Wval_33, W33, Wval_37, W37]
  ring

theorem recW_38 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ * Wval u v a b r ⟨1, 0, 0, 0, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_7, W7, Wval_13, W13, Wval_16, W16, Wval_38, W38, Wval_42, W42]
  ring

theorem recW_39 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ * Wval u v a b r ⟨1, 0, 0, 0, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_8, W8, Wval_14, W14, Wval_16, W16, Wval_39, W39, Wval_43, W43]
  ring

theorem recW_40 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 0, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_9, W9, Wval_13, W13, Wval_17, W17, Wval_40, W40, Wval_44, W44]
  ring

theorem recW_41 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 0, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_10, W10, Wval_14, W14, Wval_17, W17, Wval_41, W41, Wval_45, W45]
  ring

theorem recW_42 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_11, W11, Wval_13, W13, Wval_16, W16, Wval_34, W34, Wval_38, W38, Wval_42, W42]
  ring

theorem recW_43 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_12, W12, Wval_14, W14, Wval_16, W16, Wval_35, W35, Wval_39, W39, Wval_43, W43]
  ring

theorem recW_44 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_13, W13, Wval_17, W17, Wval_40, W40, Wval_44, W44]
  ring

theorem recW_45 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_14, W14, Wval_17, W17, Wval_41, W41, Wval_45, W45]
  ring

theorem recW_46 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 0, 0, 2⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_7, W7, Wval_18, W18, Wval_32, W32, Wval_46, W46, Wval_56, W56]
  ring

theorem recW_47 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 0, 1, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_19, W19, Wval_22, W22, Wval_32, W32, Wval_33, W33, Wval_47, W47, Wval_57, W57, Wval_60,
    W60]
  ring

theorem recW_48 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 0, 2, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_8, W8, Wval_23, W23, Wval_33, W33, Wval_48, W48, Wval_61, W61]
  ring

theorem recW_49 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 1, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_18, W18, Wval_20, W20, Wval_34, W34, Wval_38, W38, Wval_49, W49, Wval_58, W58, Wval_67,
    W67]
  ring

theorem recW_50 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 1, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_19, W19, Wval_24, W24, Wval_34, W34, Wval_39, W39, Wval_50, W50, Wval_62, W62, Wval_68,
    W68]
  ring

theorem recW_51 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 0, 2, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_9, W9, Wval_20, W20, Wval_40, W40, Wval_51, W51, Wval_69, W69]
  ring

theorem recW_52 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ * Wval u v a b r ⟨0, 0, 0, 0, 1, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_21, W21, Wval_22, W22, Wval_35, W35, Wval_38, W38, Wval_52, W52, Wval_59, W59, Wval_71,
    W71]
  ring

theorem recW_53 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 1, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_23, W23, Wval_25, W25, Wval_35, W35, Wval_39, W39, Wval_53, W53, Wval_63, W63, Wval_72,
    W72]
  ring

theorem recW_54 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 1, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_21, W21, Wval_24, W24, Wval_40, W40, Wval_41, W41, Wval_54, W54, Wval_70, W70, Wval_73,
    W73]
  ring

theorem recW_55 (u v a b r : R) :
    lhsW u v r ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ * Wval u v a b r ⟨0, 0, 0, 0, 2, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_10, W10, Wval_25, W25, Wval_41, W41, Wval_55, W55, Wval_74, W74]
  ring

theorem recW_56 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ * Wval u v a b r ⟨0, 1, 0, 1, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_18, W18, Wval_26, W26, Wval_32, W32, Wval_36, W36, Wval_46, W46, Wval_56, W56, Wval_64,
    W64]
  ring

theorem recW_57 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ * Wval u v a b r ⟨0, 1, 0, 1, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_19, W19, Wval_27, W27, Wval_33, W33, Wval_36, W36, Wval_47, W47, Wval_57, W57, Wval_65,
    W65]
  ring

theorem recW_58 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 1, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_20, W20, Wval_26, W26, Wval_34, W34, Wval_42, W42, Wval_49, W49, Wval_58, W58, Wval_75,
    W75]
  ring

theorem recW_59 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 0, 1, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_21, W21, Wval_27, W27, Wval_35, W35, Wval_42, W42, Wval_52, W52, Wval_59, W59, Wval_76,
    W76]
  ring

theorem recW_60 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ * Wval u v a b r ⟨0, 1, 1, 0, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_22, W22, Wval_27, W27, Wval_32, W32, Wval_37, W37, Wval_47, W47, Wval_60, W60, Wval_65,
    W65]
  ring

theorem recW_61 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ * Wval u v a b r ⟨0, 1, 1, 0, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_23, W23, Wval_28, W28, Wval_33, W33, Wval_37, W37, Wval_48, W48, Wval_61, W61, Wval_66,
    W66]
  ring

theorem recW_62 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ * Wval u v a b r ⟨0, 1, 1, 0, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_24, W24, Wval_27, W27, Wval_34, W34, Wval_43, W43, Wval_50, W50, Wval_62, W62, Wval_76,
    W76]
  ring

theorem recW_63 (u v a b r : R) :
    lhsW u v r ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ * Wval u v a b r ⟨0, 1, 1, 0, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_25, W25, Wval_28, W28, Wval_35, W35, Wval_43, W43, Wval_53, W53, Wval_63, W63, Wval_77,
    W77]
  ring

theorem recW_64 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_26, W26, Wval_36, W36, Wval_56, W56, Wval_64, W64]
  ring

theorem recW_65 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_27, W27, Wval_36, W36, Wval_37, W37, Wval_57, W57, Wval_60, W60, Wval_65, W65]
  ring

theorem recW_66 (u v a b r : R) :
    lhsW u v r ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_28, W28, Wval_37, W37, Wval_61, W61, Wval_66, W66]
  ring

theorem recW_67 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ * Wval u v a b r ⟨1, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_18, W18, Wval_29, W29, Wval_38, W38, Wval_42, W42, Wval_49, W49, Wval_67, W67, Wval_75,
    W75]
  ring

theorem recW_68 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ * Wval u v a b r ⟨1, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_19, W19, Wval_30, W30, Wval_39, W39, Wval_42, W42, Wval_50, W50, Wval_68, W68, Wval_76,
    W76]
  ring

theorem recW_69 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_20, W20, Wval_29, W29, Wval_40, W40, Wval_44, W44, Wval_51, W51, Wval_69, W69, Wval_78,
    W78]
  ring

theorem recW_70 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_21, W21, Wval_30, W30, Wval_41, W41, Wval_44, W44, Wval_54, W54, Wval_70, W70, Wval_79,
    W79]
  ring

theorem recW_71 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ * Wval u v a b r ⟨1, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_22, W22, Wval_30, W30, Wval_38, W38, Wval_43, W43, Wval_52, W52, Wval_71, W71, Wval_76,
    W76]
  ring

theorem recW_72 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ * Wval u v a b r ⟨1, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_23, W23, Wval_31, W31, Wval_39, W39, Wval_43, W43, Wval_53, W53, Wval_72, W72, Wval_77,
    W77]
  ring

theorem recW_73 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ * Wval u v a b r ⟨1, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_24, W24, Wval_30, W30, Wval_40, W40, Wval_45, W45, Wval_54, W54, Wval_73, W73, Wval_79,
    W79]
  ring

theorem recW_74 (u v a b r : R) :
    lhsW u v r ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ * Wval u v a b r ⟨1, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_25, W25, Wval_31, W31, Wval_41, W41, Wval_45, W45, Wval_55, W55, Wval_74, W74, Wval_80,
    W80]
  ring

theorem recW_75 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_26, W26, Wval_29, W29, Wval_42, W42, Wval_58, W58, Wval_67, W67, Wval_75, W75]
  ring

theorem recW_76 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_27, W27, Wval_30, W30, Wval_42, W42, Wval_43, W43, Wval_59, W59, Wval_62, W62, Wval_68,
    W68, Wval_71, W71, Wval_76, W76]
  ring

theorem recW_77 (u v a b r : R) :
    lhsW u v r ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_28, W28, Wval_31, W31, Wval_43, W43, Wval_63, W63, Wval_72, W72, Wval_77, W77]
  ring

theorem recW_78 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_29, W29, Wval_44, W44, Wval_69, W69, Wval_78, W78]
  ring

theorem recW_79 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_30, W30, Wval_44, W44, Wval_45, W45, Wval_70, W70, Wval_73, W73, Wval_79, W79]
  ring

theorem recW_80 (u v a b r : R) :
    lhsW u v r ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ * Wval u v a b r ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsW u v a b r (Wval u v a b r) ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsW, rhsW, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0,
    St.cc1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul,
    Wval_31, W31, Wval_45, W45, Wval_74, W74, Wval_80, W80]
  ring

theorem bdW_0 (u v a b r : R) : Wval u v a b r ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = (1 - b) := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_0, W0, Dcm]
  ring

theorem bdW_1 (u v a b r : R) : Wval u v a b r ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = b := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_1, W1, Dcm]
  ring

theorem bdW_2 (u v a b r : R) : Wval u v a b r ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = (1 - a) := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_2, W2, Dcm]
  ring

theorem bdW_3 (u v a b r : R) : Wval u v a b r ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = a := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_3, W3, Dcm]
  ring

theorem bdW_7 (u v a b r : R) : Wval u v a b r ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = (1 - a) * (1 - b) := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_7, W7, Dcm]
  ring

theorem bdW_8 (u v a b r : R) : Wval u v a b r ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = (1 - a) * b := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_8, W8, Dcm]
  ring

theorem bdW_9 (u v a b r : R) : Wval u v a b r ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = a * (1 - b) := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_9, W9, Dcm]
  ring

theorem bdW_10 (u v a b r : R) : Wval u v a b r ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
    = bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ * Dcm u v r := by
  have hb : bdryC a (1 - a) b (1 - b) ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = a * b := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Wval_10, W10, Dcm]
  ring

theorem Wval_rec (u v a b r : R) : ∀ s ∈ recStates,
    lhsW u v r s * Wval u v a b r s
      = rhsW u v a b r (Wval u v a b r) s := by
  intro s hs
  simp only [recStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [recW_4 u v a b r, recW_5 u v a b r, recW_6 u v a b r, recW_11 u v a b r, recW_12 u v a b
    r, recW_13 u v a b r, recW_14 u v a b r, recW_15 u v a b r, recW_16 u v a b r, recW_17 u v a b
    r, recW_18 u v a b r, recW_19 u v a b r, recW_20 u v a b r, recW_21 u v a b r, recW_22 u v a b
    r, recW_23 u v a b r, recW_24 u v a b r, recW_25 u v a b r, recW_26 u v a b r, recW_27 u v a b
    r, recW_28 u v a b r, recW_29 u v a b r, recW_30 u v a b r, recW_31 u v a b r, recW_32 u v a b
    r, recW_33 u v a b r, recW_34 u v a b r, recW_35 u v a b r, recW_36 u v a b r, recW_37 u v a b
    r, recW_38 u v a b r, recW_39 u v a b r, recW_40 u v a b r, recW_41 u v a b r, recW_42 u v a b
    r, recW_43 u v a b r, recW_44 u v a b r, recW_45 u v a b r, recW_46 u v a b r, recW_47 u v a b
    r, recW_48 u v a b r, recW_49 u v a b r, recW_50 u v a b r, recW_51 u v a b r, recW_52 u v a b
    r, recW_53 u v a b r, recW_54 u v a b r, recW_55 u v a b r, recW_56 u v a b r, recW_57 u v a b
    r, recW_58 u v a b r, recW_59 u v a b r, recW_60 u v a b r, recW_61 u v a b r, recW_62 u v a b
    r, recW_63 u v a b r, recW_64 u v a b r, recW_65 u v a b r, recW_66 u v a b r, recW_67 u v a b
    r, recW_68 u v a b r, recW_69 u v a b r, recW_70 u v a b r, recW_71 u v a b r, recW_72 u v a b
    r, recW_73 u v a b r, recW_74 u v a b r, recW_75 u v a b r, recW_76 u v a b r, recW_77 u v a b
    r, recW_78 u v a b r, recW_79 u v a b r, recW_80 u v a b r]

theorem Wval_bd (u v a b r : R) : ∀ s ∈ bdryStates,
    Wval u v a b r s = bdryC a (1 - a) b (1 - b) s * Dcm u v r := by
  intro s hs
  simp only [bdryStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bdW_0 u v a b r, bdW_1 u v a b r, bdW_2 u v a b r, bdW_3 u v a b r, bdW_7 u v a b r,
    bdW_8 u v a b r, bdW_9 u v a b r, bdW_10 u v a b r]

end Rhone.Algebra.BlockTwoSymbolic
