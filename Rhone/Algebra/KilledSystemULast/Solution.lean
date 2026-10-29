/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Solve

/-! # `ValU` solves the system: the 73 recursion identities and the 8 boundary conditions -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

theorem recU_4 :
    15 * lhsU ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨0, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_0, VU0, ValU_4, VU4]
  ring

theorem recU_5 :
    15 * lhsU ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨0, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_0, VU0, ValU_1, VU1,
    ValU_5, VU5]
  ring

theorem recU_6 :
    15 * lhsU ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_1, VU1, ValU_6, VU6]
  ring

theorem recU_11 :
    15 * lhsU ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ * ValU ⟨0, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_0, VU0, ValU_2, VU2,
    ValU_7, VU7, ValU_11, VU11]
  ring

theorem recU_12 :
    15 * lhsU ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_1, VU1, ValU_2, VU2,
    ValU_8, VU8, ValU_12, VU12]
  ring

theorem recU_13 :
    15 * lhsU ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ * ValU ⟨1, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_0, VU0, ValU_3, VU3,
    ValU_9, VU9, ValU_13, VU13]
  ring

theorem recU_14 :
    15 * lhsU ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ * ValU ⟨1, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_1, VU1, ValU_3, VU3,
    ValU_10, VU10, ValU_14, VU14]
  ring

theorem recU_15 :
    15 * lhsU ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 0, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_2, VU2, ValU_15,
    VU15]
  ring

theorem recU_16 :
    15 * lhsU ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_2, VU2, ValU_3, VU3,
    ValU_16, VU16]
  ring

theorem recU_17 :
    15 * lhsU ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 0, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_3, VU3, ValU_17,
    VU17]
  ring

theorem recU_18 :
    15 * lhsU ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ * ValU ⟨0, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_4, VU4, ValU_7, VU7,
    ValU_11, VU11, ValU_18, VU18, ValU_26, VU26]
  ring

theorem recU_19 :
    15 * lhsU ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ * ValU ⟨0, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_8, VU8,
    ValU_11, VU11, ValU_19, VU19, ValU_27, VU27]
  ring

theorem recU_20 :
    15 * lhsU ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ * ValU ⟨0, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_4, VU4, ValU_9, VU9,
    ValU_13, VU13, ValU_20, VU20, ValU_29, VU29]
  ring

theorem recU_21 :
    15 * lhsU ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ * ValU ⟨0, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_10,
    VU10, ValU_13, VU13, ValU_21, VU21, ValU_30, VU30]
  ring

theorem recU_22 :
    15 * lhsU ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ * ValU ⟨0, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_7, VU7,
    ValU_12, VU12, ValU_22, VU22, ValU_27, VU27]
  ring

theorem recU_23 :
    15 * lhsU ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ * ValU ⟨0, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_6, VU6, ValU_8, VU8,
    ValU_12, VU12, ValU_23, VU23, ValU_28, VU28]
  ring

theorem recU_24 :
    15 * lhsU ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ * ValU ⟨0, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_9, VU9,
    ValU_14, VU14, ValU_24, VU24, ValU_30, VU30]
  ring

theorem recU_25 :
    15 * lhsU ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ * ValU ⟨0, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_6, VU6, ValU_10,
    VU10, ValU_14, VU14, ValU_25, VU25, ValU_31, VU31]
  ring

theorem recU_26 :
    15 * lhsU ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨0, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_4, VU4, ValU_11,
    VU11, ValU_18, VU18, ValU_26, VU26]
  ring

theorem recU_27 :
    15 * lhsU ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_11,
    VU11, ValU_12, VU12, ValU_19, VU19, ValU_22, VU22, ValU_27, VU27]
  ring

theorem recU_28 :
    15 * lhsU ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_6, VU6, ValU_12,
    VU12, ValU_23, VU23, ValU_28, VU28]
  ring

theorem recU_29 :
    15 * lhsU ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨1, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_4, VU4, ValU_13,
    VU13, ValU_20, VU20, ValU_29, VU29]
  ring

theorem recU_30 :
    15 * lhsU ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨1, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_5, VU5, ValU_13,
    VU13, ValU_14, VU14, ValU_21, VU21, ValU_24, VU24, ValU_30, VU30]
  ring

theorem recU_31 :
    15 * lhsU ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨1, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_6, VU6, ValU_14,
    VU14, ValU_25, VU25, ValU_31, VU31]
  ring

theorem recU_32 :
    15 * lhsU ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ * ValU ⟨0, 1, 0, 0, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_7, VU7, ValU_11,
    VU11, ValU_15, VU15, ValU_32, VU32, ValU_36, VU36]
  ring

theorem recU_33 :
    15 * lhsU ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ * ValU ⟨0, 1, 0, 0, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_8, VU8, ValU_12,
    VU12, ValU_15, VU15, ValU_33, VU33, ValU_37, VU37]
  ring

theorem recU_34 :
    15 * lhsU ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ * ValU ⟨0, 1, 0, 0, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_9, VU9, ValU_11,
    VU11, ValU_16, VU16, ValU_34, VU34, ValU_42, VU42]
  ring

theorem recU_35 :
    15 * lhsU ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ * ValU ⟨0, 1, 0, 0, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_10, VU10, ValU_12,
    VU12, ValU_16, VU16, ValU_35, VU35, ValU_43, VU43]
  ring

theorem recU_36 :
    15 * lhsU ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 0, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_11, VU11, ValU_15,
    VU15, ValU_32, VU32, ValU_36, VU36]
  ring

theorem recU_37 :
    15 * lhsU ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 1, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_12, VU12, ValU_15,
    VU15, ValU_33, VU33, ValU_37, VU37]
  ring

theorem recU_38 :
    15 * lhsU ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ * ValU ⟨1, 0, 0, 0, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_7, VU7, ValU_13,
    VU13, ValU_16, VU16, ValU_38, VU38, ValU_42, VU42]
  ring

theorem recU_39 :
    15 * lhsU ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ * ValU ⟨1, 0, 0, 0, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_8, VU8, ValU_14,
    VU14, ValU_16, VU16, ValU_39, VU39, ValU_43, VU43]
  ring

theorem recU_40 :
    15 * lhsU ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ * ValU ⟨1, 0, 0, 0, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_9, VU9, ValU_13,
    VU13, ValU_17, VU17, ValU_40, VU40, ValU_44, VU44]
  ring

theorem recU_41 :
    15 * lhsU ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ * ValU ⟨1, 0, 0, 0, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_10, VU10, ValU_14,
    VU14, ValU_17, VU17, ValU_41, VU41, ValU_45, VU45]
  ring

theorem recU_42 :
    15 * lhsU ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_11, VU11, ValU_13,
    VU13, ValU_16, VU16, ValU_34, VU34, ValU_38, VU38, ValU_42, VU42]
  ring

theorem recU_43 :
    15 * lhsU ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_12, VU12, ValU_14,
    VU14, ValU_16, VU16, ValU_35, VU35, ValU_39, VU39, ValU_43, VU43]
  ring

theorem recU_44 :
    15 * lhsU ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_13, VU13, ValU_17,
    VU17, ValU_40, VU40, ValU_44, VU44]
  ring

theorem recU_45 :
    15 * lhsU ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_14, VU14, ValU_17,
    VU17, ValU_41, VU41, ValU_45, VU45]
  ring

theorem recU_46 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ * ValU ⟨0, 0, 0, 0, 0, 0, 0, 2⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_7, VU7, ValU_18,
    VU18, ValU_32, VU32, ValU_46, VU46, ValU_56, VU56]
  ring

theorem recU_47 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ * ValU ⟨0, 0, 0, 0, 0, 0, 1, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_19, VU19, ValU_22,
    VU22, ValU_32, VU32, ValU_33, VU33, ValU_47, VU47, ValU_57, VU57, ValU_60, VU60]
  ring

theorem recU_48 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ * ValU ⟨0, 0, 0, 0, 0, 0, 2, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_8, VU8, ValU_23,
    VU23, ValU_33, VU33, ValU_48, VU48, ValU_61, VU61]
  ring

theorem recU_49 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ * ValU ⟨0, 0, 0, 0, 0, 1, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_18, VU18, ValU_20,
    VU20, ValU_34, VU34, ValU_38, VU38, ValU_49, VU49, ValU_58, VU58, ValU_67, VU67]
  ring

theorem recU_50 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ * ValU ⟨0, 0, 0, 0, 0, 1, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_19, VU19, ValU_24,
    VU24, ValU_34, VU34, ValU_39, VU39, ValU_50, VU50, ValU_62, VU62, ValU_68, VU68]
  ring

theorem recU_51 :
    15 * lhsU ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ * ValU ⟨0, 0, 0, 0, 0, 2, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_9, VU9, ValU_20,
    VU20, ValU_40, VU40, ValU_51, VU51, ValU_69, VU69]
  ring

theorem recU_52 :
    15 * lhsU ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ * ValU ⟨0, 0, 0, 0, 1, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_21, VU21, ValU_22,
    VU22, ValU_35, VU35, ValU_38, VU38, ValU_52, VU52, ValU_59, VU59, ValU_71, VU71]
  ring

theorem recU_53 :
    15 * lhsU ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ * ValU ⟨0, 0, 0, 0, 1, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_23, VU23, ValU_25,
    VU25, ValU_35, VU35, ValU_39, VU39, ValU_53, VU53, ValU_63, VU63, ValU_72, VU72]
  ring

theorem recU_54 :
    15 * lhsU ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ * ValU ⟨0, 0, 0, 0, 1, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_21, VU21, ValU_24,
    VU24, ValU_40, VU40, ValU_41, VU41, ValU_54, VU54, ValU_70, VU70, ValU_73, VU73]
  ring

theorem recU_55 :
    15 * lhsU ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ * ValU ⟨0, 0, 0, 0, 2, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_10, VU10, ValU_25,
    VU25, ValU_41, VU41, ValU_55, VU55, ValU_74, VU74]
  ring

theorem recU_56 :
    15 * lhsU ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ * ValU ⟨0, 1, 0, 1, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_18, VU18, ValU_26,
    VU26, ValU_32, VU32, ValU_36, VU36, ValU_46, VU46, ValU_56, VU56, ValU_64, VU64]
  ring

theorem recU_57 :
    15 * lhsU ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ * ValU ⟨0, 1, 0, 1, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_19, VU19, ValU_27,
    VU27, ValU_33, VU33, ValU_36, VU36, ValU_47, VU47, ValU_57, VU57, ValU_65, VU65]
  ring

theorem recU_58 :
    15 * lhsU ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ * ValU ⟨0, 1, 0, 1, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_20, VU20, ValU_26,
    VU26, ValU_34, VU34, ValU_42, VU42, ValU_49, VU49, ValU_58, VU58, ValU_75, VU75]
  ring

theorem recU_59 :
    15 * lhsU ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ * ValU ⟨0, 1, 0, 1, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_21, VU21, ValU_27,
    VU27, ValU_35, VU35, ValU_42, VU42, ValU_52, VU52, ValU_59, VU59, ValU_76, VU76]
  ring

theorem recU_60 :
    15 * lhsU ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ * ValU ⟨0, 1, 1, 0, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_22, VU22, ValU_27,
    VU27, ValU_32, VU32, ValU_37, VU37, ValU_47, VU47, ValU_60, VU60, ValU_65, VU65]
  ring

theorem recU_61 :
    15 * lhsU ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ * ValU ⟨0, 1, 1, 0, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_23, VU23, ValU_28,
    VU28, ValU_33, VU33, ValU_37, VU37, ValU_48, VU48, ValU_61, VU61, ValU_66, VU66]
  ring

theorem recU_62 :
    15 * lhsU ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ * ValU ⟨0, 1, 1, 0, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_24, VU24, ValU_27,
    VU27, ValU_34, VU34, ValU_43, VU43, ValU_50, VU50, ValU_62, VU62, ValU_76, VU76]
  ring

theorem recU_63 :
    15 * lhsU ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ * ValU ⟨0, 1, 1, 0, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_25, VU25, ValU_28,
    VU28, ValU_35, VU35, ValU_43, VU43, ValU_53, VU53, ValU_63, VU63, ValU_77, VU77]
  ring

theorem recU_64 :
    15 * lhsU ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_26, VU26, ValU_36,
    VU36, ValU_56, VU56, ValU_64, VU64]
  ring

theorem recU_65 :
    15 * lhsU ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_27, VU27, ValU_36,
    VU36, ValU_37, VU37, ValU_57, VU57, ValU_60, VU60, ValU_65, VU65]
  ring

theorem recU_66 :
    15 * lhsU ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_28, VU28, ValU_37,
    VU37, ValU_61, VU61, ValU_66, VU66]
  ring

theorem recU_67 :
    15 * lhsU ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ * ValU ⟨1, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_18, VU18, ValU_29,
    VU29, ValU_38, VU38, ValU_42, VU42, ValU_49, VU49, ValU_67, VU67, ValU_75, VU75]
  ring

theorem recU_68 :
    15 * lhsU ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ * ValU ⟨1, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_19, VU19, ValU_30,
    VU30, ValU_39, VU39, ValU_42, VU42, ValU_50, VU50, ValU_68, VU68, ValU_76, VU76]
  ring

theorem recU_69 :
    15 * lhsU ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ * ValU ⟨1, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_20, VU20, ValU_29,
    VU29, ValU_40, VU40, ValU_44, VU44, ValU_51, VU51, ValU_69, VU69, ValU_78, VU78]
  ring

theorem recU_70 :
    15 * lhsU ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ * ValU ⟨1, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_21, VU21, ValU_30,
    VU30, ValU_41, VU41, ValU_44, VU44, ValU_54, VU54, ValU_70, VU70, ValU_79, VU79]
  ring

theorem recU_71 :
    15 * lhsU ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ * ValU ⟨1, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_22, VU22, ValU_30,
    VU30, ValU_38, VU38, ValU_43, VU43, ValU_52, VU52, ValU_71, VU71, ValU_76, VU76]
  ring

theorem recU_72 :
    15 * lhsU ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ * ValU ⟨1, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_23, VU23, ValU_31,
    VU31, ValU_39, VU39, ValU_43, VU43, ValU_53, VU53, ValU_72, VU72, ValU_77, VU77]
  ring

theorem recU_73 :
    15 * lhsU ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ * ValU ⟨1, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_24, VU24, ValU_30,
    VU30, ValU_40, VU40, ValU_45, VU45, ValU_54, VU54, ValU_73, VU73, ValU_79, VU79]
  ring

theorem recU_74 :
    15 * lhsU ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ * ValU ⟨1, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_25, VU25, ValU_31,
    VU31, ValU_41, VU41, ValU_45, VU45, ValU_55, VU55, ValU_74, VU74, ValU_80, VU80]
  ring

theorem recU_75 :
    15 * lhsU ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_26, VU26, ValU_29,
    VU29, ValU_42, VU42, ValU_58, VU58, ValU_67, VU67, ValU_75, VU75]
  ring

theorem recU_76 :
    15 * lhsU ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_27, VU27, ValU_30,
    VU30, ValU_42, VU42, ValU_43, VU43, ValU_59, VU59, ValU_62, VU62, ValU_68, VU68, ValU_71,
    VU71, ValU_76, VU76]
  ring

theorem recU_77 :
    15 * lhsU ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_28, VU28, ValU_31,
    VU31, ValU_43, VU43, ValU_63, VU63, ValU_72, VU72, ValU_77, VU77]
  ring

theorem recU_78 :
    15 * lhsU ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_29, VU29, ValU_44,
    VU44, ValU_69, VU69, ValU_78, VU78]
  ring

theorem recU_79 :
    15 * lhsU ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_30, VU30, ValU_44,
    VU44, ValU_45, VU45, ValU_70, VU70, ValU_73, VU73, ValU_79, VU79]
  ring

theorem recU_80 :
    15 * lhsU ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ * ValU ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU
          ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsU, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    tAU, tBU, rhoPU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, ValU_31, VU31, ValU_45,
    VU45, ValU_74, VU74, ValU_80, VU80]
  ring

theorem bdU_0 : ValU ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_0, VU0, DcomU, piB1F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_1 : ValU ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_1, VU1, DcomU, piB0F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_2 : ValU ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = piA1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_2, VU2, DcomU, piA1F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_3 : ValU ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = piA0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_3, VU3, DcomU, piA0F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_7 : ValU ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = piA1F * piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_7, VU7, DcomU, piA1F, piB1F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_8 : ValU ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = piA1F * piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_8, VU8, DcomU, piA1F, piB0F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_9 : ValU ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = piA0F * piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_9, VU9, DcomU, piA0F, piB1F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bdU_10 : ValU ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩) * DcomU := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = piA0F * piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [ValU_10, VU10, DcomU, piA0F, piB0F]
  exact quint_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem ValU_rec : ∀ s ∈ recStates,
    15 * lhsU s * ValU s
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) ValU s := by
  intro s hs
  simp only [recStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [recU_4, recU_5, recU_6, recU_11, recU_12, recU_13, recU_14, recU_15, recU_16, recU_17,
    recU_18, recU_19, recU_20, recU_21, recU_22, recU_23, recU_24, recU_25, recU_26, recU_27,
    recU_28, recU_29, recU_30, recU_31, recU_32, recU_33, recU_34, recU_35, recU_36, recU_37,
    recU_38, recU_39, recU_40, recU_41, recU_42, recU_43, recU_44, recU_45, recU_46, recU_47,
    recU_48, recU_49, recU_50, recU_51, recU_52, recU_53, recU_54, recU_55, recU_56, recU_57,
    recU_58, recU_59, recU_60, recU_61, recU_62, recU_63, recU_64, recU_65, recU_66, recU_67,
    recU_68, recU_69, recU_70, recU_71, recU_72, recU_73, recU_74, recU_75, recU_76, recU_77,
    recU_78, recU_79, recU_80]

theorem ValU_bd : ∀ s ∈ bdryStates,
    ValU s = C (bdryC piA0F piA1F piB0F piB1F s) * DcomU := by
  intro s hs
  simp only [bdryStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bdU_0, bdU_1, bdU_2, bdU_3, bdU_7, bdU_8, bdU_9, bdU_10]

theorem qSolU_isSolutionU : IsSolutionU qSolU :=
  isSolutionU_of_poly ValU DcomU DcomU_ne_zero ValU_rec ValU_bd

end Rhone.Algebra.KilledSystemULast
