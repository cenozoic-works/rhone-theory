/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Solve

/-! # `Val` solves the system: the 73 recursion identities and the 8 boundary conditions -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

open Polynomial

theorem rec_4 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ * Val ⟨0, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_0, V0, Val_4, V4]
  ring

theorem rec_5 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ * Val ⟨0, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_0, V0, Val_1, V1, Val_5, V5]
  ring

theorem rec_6 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ * Val ⟨0, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_1, V1, Val_6, V6]
  ring

theorem rec_11 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ * Val ⟨0, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_0, V0, Val_2, V2, Val_7, V7,
    Val_11, V11]
  ring

theorem rec_12 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ * Val ⟨0, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_1, V1, Val_2, V2, Val_8, V8,
    Val_12, V12]
  ring

theorem rec_13 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ * Val ⟨1, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_0, V0, Val_3, V3, Val_9, V9,
    Val_13, V13]
  ring

theorem rec_14 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ * Val ⟨1, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_1, V1, Val_3, V3, Val_10, V10,
    Val_14, V14]
  ring

theorem rec_15 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ * Val ⟨0, 2, 0, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_2, V2, Val_15, V15]
  ring

theorem rec_16 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ * Val ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_2, V2, Val_3, V3, Val_16, V16]
  ring

theorem rec_17 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ * Val ⟨2, 0, 0, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_3, V3, Val_17, V17]
  ring

theorem rec_18 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ * Val ⟨0, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_4, V4, Val_7, V7, Val_11, V11,
    Val_18, V18, Val_26, V26]
  ring

theorem rec_19 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ * Val ⟨0, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_8, V8, Val_11, V11,
    Val_19, V19, Val_27, V27]
  ring

theorem rec_20 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ * Val ⟨0, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_4, V4, Val_9, V9, Val_13, V13,
    Val_20, V20, Val_29, V29]
  ring

theorem rec_21 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ * Val ⟨0, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_10, V10, Val_13,
    V13, Val_21, V21, Val_30, V30]
  ring

theorem rec_22 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ * Val ⟨0, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_7, V7, Val_12, V12,
    Val_22, V22, Val_27, V27]
  ring

theorem rec_23 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ * Val ⟨0, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_6, V6, Val_8, V8, Val_12, V12,
    Val_23, V23, Val_28, V28]
  ring

theorem rec_24 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ * Val ⟨0, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_9, V9, Val_14, V14,
    Val_24, V24, Val_30, V30]
  ring

theorem rec_25 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ * Val ⟨0, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_6, V6, Val_10, V10, Val_14,
    V14, Val_25, V25, Val_31, V31]
  ring

theorem rec_26 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ * Val ⟨0, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_4, V4, Val_11, V11, Val_18,
    V18, Val_26, V26]
  ring

theorem rec_27 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ * Val ⟨0, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_11, V11, Val_12,
    V12, Val_19, V19, Val_22, V22, Val_27, V27]
  ring

theorem rec_28 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ * Val ⟨0, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_6, V6, Val_12, V12, Val_23,
    V23, Val_28, V28]
  ring

theorem rec_29 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ * Val ⟨1, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_4, V4, Val_13, V13, Val_20,
    V20, Val_29, V29]
  ring

theorem rec_30 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ * Val ⟨1, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_5, V5, Val_13, V13, Val_14,
    V14, Val_21, V21, Val_24, V24, Val_30, V30]
  ring

theorem rec_31 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ * Val ⟨1, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_6, V6, Val_14, V14, Val_25,
    V25, Val_31, V31]
  ring

theorem rec_32 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ * Val ⟨0, 1, 0, 0, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_7, V7, Val_11, V11, Val_15,
    V15, Val_32, V32, Val_36, V36]
  ring

theorem rec_33 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ * Val ⟨0, 1, 0, 0, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_8, V8, Val_12, V12, Val_15,
    V15, Val_33, V33, Val_37, V37]
  ring

theorem rec_34 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ * Val ⟨0, 1, 0, 0, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_9, V9, Val_11, V11, Val_16,
    V16, Val_34, V34, Val_42, V42]
  ring

theorem rec_35 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ * Val ⟨0, 1, 0, 0, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_10, V10, Val_12, V12, Val_16,
    V16, Val_35, V35, Val_43, V43]
  ring

theorem rec_36 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ * Val ⟨0, 2, 0, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_11, V11, Val_15, V15, Val_32,
    V32, Val_36, V36]
  ring

theorem rec_37 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ * Val ⟨0, 2, 1, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_12, V12, Val_15, V15, Val_33,
    V33, Val_37, V37]
  ring

theorem rec_38 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ * Val ⟨1, 0, 0, 0, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_7, V7, Val_13, V13, Val_16,
    V16, Val_38, V38, Val_42, V42]
  ring

theorem rec_39 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ * Val ⟨1, 0, 0, 0, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_8, V8, Val_14, V14, Val_16,
    V16, Val_39, V39, Val_43, V43]
  ring

theorem rec_40 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ * Val ⟨1, 0, 0, 0, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_9, V9, Val_13, V13, Val_17,
    V17, Val_40, V40, Val_44, V44]
  ring

theorem rec_41 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ * Val ⟨1, 0, 0, 0, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_10, V10, Val_14, V14, Val_17,
    V17, Val_41, V41, Val_45, V45]
  ring

theorem rec_42 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ * Val ⟨1, 1, 0, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_11, V11, Val_13, V13, Val_16,
    V16, Val_34, V34, Val_38, V38, Val_42, V42]
  ring

theorem rec_43 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ * Val ⟨1, 1, 1, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_12, V12, Val_14, V14, Val_16,
    V16, Val_35, V35, Val_39, V39, Val_43, V43]
  ring

theorem rec_44 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ * Val ⟨2, 0, 0, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_13, V13, Val_17, V17, Val_40,
    V40, Val_44, V44]
  ring

theorem rec_45 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ * Val ⟨2, 0, 1, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_14, V14, Val_17, V17, Val_41,
    V41, Val_45, V45]
  ring

theorem rec_46 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ * Val ⟨0, 0, 0, 0, 0, 0, 0, 2⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_7, V7, Val_18, V18, Val_32,
    V32, Val_46, V46, Val_56, V56]
  ring

theorem rec_47 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ * Val ⟨0, 0, 0, 0, 0, 0, 1, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_19, V19, Val_22, V22, Val_32,
    V32, Val_33, V33, Val_47, V47, Val_57, V57, Val_60, V60]
  ring

theorem rec_48 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ * Val ⟨0, 0, 0, 0, 0, 0, 2, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_8, V8, Val_23, V23, Val_33,
    V33, Val_48, V48, Val_61, V61]
  ring

theorem rec_49 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ * Val ⟨0, 0, 0, 0, 0, 1, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_18, V18, Val_20, V20, Val_34,
    V34, Val_38, V38, Val_49, V49, Val_58, V58, Val_67, V67]
  ring

theorem rec_50 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ * Val ⟨0, 0, 0, 0, 0, 1, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_19, V19, Val_24, V24, Val_34,
    V34, Val_39, V39, Val_50, V50, Val_62, V62, Val_68, V68]
  ring

theorem rec_51 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ * Val ⟨0, 0, 0, 0, 0, 2, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_9, V9, Val_20, V20, Val_40,
    V40, Val_51, V51, Val_69, V69]
  ring

theorem rec_52 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ * Val ⟨0, 0, 0, 0, 1, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_21, V21, Val_22, V22, Val_35,
    V35, Val_38, V38, Val_52, V52, Val_59, V59, Val_71, V71]
  ring

theorem rec_53 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ * Val ⟨0, 0, 0, 0, 1, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_23, V23, Val_25, V25, Val_35,
    V35, Val_39, V39, Val_53, V53, Val_63, V63, Val_72, V72]
  ring

theorem rec_54 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ * Val ⟨0, 0, 0, 0, 1, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_21, V21, Val_24, V24, Val_40,
    V40, Val_41, V41, Val_54, V54, Val_70, V70, Val_73, V73]
  ring

theorem rec_55 :
    15 * lhsC thAP thBP rhoP ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ * Val ⟨0, 0, 0, 0, 2, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_10, V10, Val_25, V25, Val_41,
    V41, Val_55, V55, Val_74, V74]
  ring

theorem rec_56 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ * Val ⟨0, 1, 0, 1, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_18, V18, Val_26, V26, Val_32,
    V32, Val_36, V36, Val_46, V46, Val_56, V56, Val_64, V64]
  ring

theorem rec_57 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ * Val ⟨0, 1, 0, 1, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_19, V19, Val_27, V27, Val_33,
    V33, Val_36, V36, Val_47, V47, Val_57, V57, Val_65, V65]
  ring

theorem rec_58 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ * Val ⟨0, 1, 0, 1, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_20, V20, Val_26, V26, Val_34,
    V34, Val_42, V42, Val_49, V49, Val_58, V58, Val_75, V75]
  ring

theorem rec_59 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ * Val ⟨0, 1, 0, 1, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_21, V21, Val_27, V27, Val_35,
    V35, Val_42, V42, Val_52, V52, Val_59, V59, Val_76, V76]
  ring

theorem rec_60 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ * Val ⟨0, 1, 1, 0, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_22, V22, Val_27, V27, Val_32,
    V32, Val_37, V37, Val_47, V47, Val_60, V60, Val_65, V65]
  ring

theorem rec_61 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ * Val ⟨0, 1, 1, 0, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_23, V23, Val_28, V28, Val_33,
    V33, Val_37, V37, Val_48, V48, Val_61, V61, Val_66, V66]
  ring

theorem rec_62 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ * Val ⟨0, 1, 1, 0, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_24, V24, Val_27, V27, Val_34,
    V34, Val_43, V43, Val_50, V50, Val_62, V62, Val_76, V76]
  ring

theorem rec_63 :
    15 * lhsC thAP thBP rhoP ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ * Val ⟨0, 1, 1, 0, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_25, V25, Val_28, V28, Val_35,
    V35, Val_43, V43, Val_53, V53, Val_63, V63, Val_77, V77]
  ring

theorem rec_64 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ * Val ⟨0, 2, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_26, V26, Val_36, V36, Val_56,
    V56, Val_64, V64]
  ring

theorem rec_65 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ * Val ⟨0, 2, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_27, V27, Val_36, V36, Val_37,
    V37, Val_57, V57, Val_60, V60, Val_65, V65]
  ring

theorem rec_66 :
    15 * lhsC thAP thBP rhoP ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ * Val ⟨0, 2, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_28, V28, Val_37, V37, Val_61,
    V61, Val_66, V66]
  ring

theorem rec_67 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ * Val ⟨1, 0, 0, 1, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_18, V18, Val_29, V29, Val_38,
    V38, Val_42, V42, Val_49, V49, Val_67, V67, Val_75, V75]
  ring

theorem rec_68 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ * Val ⟨1, 0, 0, 1, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_19, V19, Val_30, V30, Val_39,
    V39, Val_42, V42, Val_50, V50, Val_68, V68, Val_76, V76]
  ring

theorem rec_69 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ * Val ⟨1, 0, 0, 1, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_20, V20, Val_29, V29, Val_40,
    V40, Val_44, V44, Val_51, V51, Val_69, V69, Val_78, V78]
  ring

theorem rec_70 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ * Val ⟨1, 0, 0, 1, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_21, V21, Val_30, V30, Val_41,
    V41, Val_44, V44, Val_54, V54, Val_70, V70, Val_79, V79]
  ring

theorem rec_71 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ * Val ⟨1, 0, 1, 0, 0, 0, 0, 1⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_22, V22, Val_30, V30, Val_38,
    V38, Val_43, V43, Val_52, V52, Val_71, V71, Val_76, V76]
  ring

theorem rec_72 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ * Val ⟨1, 0, 1, 0, 0, 0, 1, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_23, V23, Val_31, V31, Val_39,
    V39, Val_43, V43, Val_53, V53, Val_72, V72, Val_77, V77]
  ring

theorem rec_73 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ * Val ⟨1, 0, 1, 0, 0, 1, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_24, V24, Val_30, V30, Val_40,
    V40, Val_45, V45, Val_54, V54, Val_73, V73, Val_79, V79]
  ring

theorem rec_74 :
    15 * lhsC thAP thBP rhoP ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ * Val ⟨1, 0, 1, 0, 1, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_25, V25, Val_31, V31, Val_41,
    V41, Val_45, V45, Val_55, V55, Val_74, V74, Val_80, V80]
  ring

theorem rec_75 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ * Val ⟨1, 1, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_26, V26, Val_29, V29, Val_42,
    V42, Val_58, V58, Val_67, V67, Val_75, V75]
  ring

theorem rec_76 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ * Val ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_27, V27, Val_30, V30, Val_42,
    V42, Val_43, V43, Val_59, V59, Val_62, V62, Val_68, V68, Val_71, V71, Val_76, V76]
  ring

theorem rec_77 :
    15 * lhsC thAP thBP rhoP ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ * Val ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_28, V28, Val_31, V31, Val_43,
    V43, Val_63, V63, Val_72, V72, Val_77, V77]
  ring

theorem rec_78 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ * Val ⟨2, 0, 0, 2, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_29, V29, Val_44, V44, Val_69,
    V69, Val_78, V78]
  ring

theorem rec_79 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ * Val ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_30, V30, Val_44, V44, Val_45,
    V45, Val_70, V70, Val_73, V73, Val_79, V79]
  ring

theorem rec_80 :
    15 * lhsC thAP thBP rhoP ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ * Val ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val
          ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ := by
  simp only [rterms, lhsC, rhsC, pfac, St.n, St.nA, St.nB, St.t, St.cr0, St.cr1, St.cc0, St.cc1,
    thAP, thBP, rhoP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMul, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Val_31, V31, Val_45, V45, Val_74,
    V74, Val_80, V80]
  ring

theorem bd_0 : Val ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_0, V0, Dcom, piB1F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_1 : Val ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_1, V1, Dcom, piB0F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_2 : Val ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = piA1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_2, V2, Dcom, piA1F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_3 : Val ⟨1, 0, 0, 0, 0, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = piA0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_3, V3, Dcom, piA0F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_7 : Val ⟨0, 0, 0, 0, 0, 0, 0, 1⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = piA1F * piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_7, V7, Dcom, piA1F, piB1F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_8 : Val ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = piA1F * piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_8, V8, Dcom, piA1F, piB0F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_9 : Val ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = piA0F * piB1F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_9, V9, Dcom, piA0F, piB1F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem bd_10 : Val ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
    = C (bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩) * Dcom := by
  have hb : bdryC piA0F piA1F piB0F piB1F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = piA0F * piB0F := by
    simp only [bdryC]
    norm_num
  rw [hb]
  simp only [Val_10, V10, Dcom, piA0F, piB0F]
  exact quad_smul _ _ _ _ _ _ _ (by ring) (by ring) (by ring)

theorem Val_rec : ∀ s ∈ recStates,
    15 * lhsC thAP thBP rhoP s * Val s
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) Val s := by
  intro s hs
  simp only [recStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [rec_4, rec_5, rec_6, rec_11, rec_12, rec_13, rec_14, rec_15, rec_16, rec_17, rec_18,
    rec_19, rec_20, rec_21, rec_22, rec_23, rec_24, rec_25, rec_26, rec_27, rec_28, rec_29,
    rec_30, rec_31, rec_32, rec_33, rec_34, rec_35, rec_36, rec_37, rec_38, rec_39, rec_40,
    rec_41, rec_42, rec_43, rec_44, rec_45, rec_46, rec_47, rec_48, rec_49, rec_50, rec_51,
    rec_52, rec_53, rec_54, rec_55, rec_56, rec_57, rec_58, rec_59, rec_60, rec_61, rec_62,
    rec_63, rec_64, rec_65, rec_66, rec_67, rec_68, rec_69, rec_70, rec_71, rec_72, rec_73,
    rec_74, rec_75, rec_76, rec_77, rec_78, rec_79, rec_80]

theorem Val_bd : ∀ s ∈ bdryStates,
    Val s = C (bdryC piA0F piA1F piB0F piB1F s) * Dcom := by
  intro s hs
  simp only [bdryStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bd_0, bd_1, bd_2, bd_3, bd_7, bd_8, bd_9, bd_10]

theorem qSol_isSolution : IsSolution qSol :=
  isSolution_of_poly Val Dcom Dcom_ne_zero Val_rec Val_bd

end Rhone.Algebra.KilledSystem
