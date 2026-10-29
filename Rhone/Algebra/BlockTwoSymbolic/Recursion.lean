/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Recursion

/-! # The killed-PIM system with symbolic mutant frequencies: integral parameters -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open KilledSystem

variable {R : Type*} [CommRing R]

def lhsW (u v r : R) (s : St) : R :=
  2 * ((s.n * (s.n - 1) : ℕ) : R) + (u + v) * (s.nA : ℕ) + (u - v) * (s.nB : ℕ)
    + 2 * r * (s.t : ℕ)

def rhsW (u v a b r : R) (q : St → R) (s : St) : R :=
  rhsC 2 ((u + v) * a) ((u + v) * (1 - a)) ((u - v) * b) ((u - v) * (1 - b)) (2 * r) q s

theorem lhsW_eq (tA tB r : R) (s : St) :
    lhsW (tA + tB) (tA - tB) r s = 2 * lhsC tA tB r s := by
  simp only [lhsW, lhsC]
  ring

end Rhone.Algebra.BlockTwoSymbolic
