/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Recursion
public import Rhone.Algebra.NoDegreeTwoFormula

/-! # The killed-PIM system in the `u`-last reading of the tower -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

def IsSolutionU (q : St → L) : Prop :=
  (∀ s ∈ recStates, lhsC thAu thBu rhoU s * q s
      = rhsC 1 (thAu * piA0) (thAu * piA1) (thBu * piB0) (thBu * piB1) rhoU q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC piA0 piA1 piB0 piB1 s)

noncomputable def tAU : P := X + C vv

noncomputable def tBU : P := X - C vv

noncomputable def rhoPU : P := C rhoM

theorem C_two_P : (C (2 : Fuv) : P) = 2 := map_ofNat Polynomial.C 2

theorem tAU_eq : tAU = 2 * (C (2 : Fuv)⁻¹ * (X + C vv)) := by
  rw [tAU, ← C_two_P, ← mul_assoc, ← map_mul]
  norm_num

theorem tBU_eq : tBU = 2 * (C (2 : Fuv)⁻¹ * (X - C vv)) := by
  rw [tBU, ← C_two_P, ← mul_assoc, ← map_mul]
  norm_num

@[simp] theorem algebraMap_tAU : algebraMap P L tAU = 2 * thAu := by
  rw [tAU_eq, map_mul, map_ofNat, thAu]

@[simp] theorem algebraMap_tBU : algebraMap P L tBU = 2 * thBu := by
  rw [tBU_eq, map_mul, map_ofNat, thBu]

@[simp] theorem algebraMap_rhoPU : algebraMap P L rhoPU = rhoU := RatFunc.algebraMap_C _

noncomputable def lhsU (s : St) : P :=
  2 * ((s.n * (s.n - 1) : ℕ) : P) + tAU * (s.nA : ℕ) + tBU * (s.nB : ℕ)
    + 2 * rhoPU * (s.t : ℕ)

theorem algebraMap_lhsU (s : St) :
    algebraMap P L (lhsU s) = 2 * lhsC thAu thBu rhoU s := by
  simp only [lhsU, lhsC, map_add, map_mul, map_ofNat, map_natCast, algebraMap_tAU,
    algebraMap_tBU, algebraMap_rhoPU]
  ring

end Rhone.Algebra.KilledSystemULast
