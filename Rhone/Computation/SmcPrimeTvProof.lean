/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SmcPrimeTv
public import Rhone.Coalescent.SmcBound.Bounds
public import Mathlib.Data.Rat.Cast.Order

/-! # Real-cast identities for the unchanged finite bound recurrences -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTv

theorem hazard_cast (R : Rat) (j : Nat) :
    (hazard R j : Real) = Rhone.Coalescent.SmcBound.hazard (R : Real) j := by
  simp [hazard, Rhone.Coalescent.SmcBound.hazard]

theorem raceBound_cast (R : Rat) (m : Nat) :
    (raceBound R m : Real) =
      Rhone.Coalescent.SmcBound.raceBound (Rhone.Coalescent.SmcBound.hazard (R : Real)) m := by
  induction m with
  | zero => simp [raceBound, Rhone.Coalescent.SmcBound.raceBound]
  | succ m ih =>
    simp [raceBound, Rhone.Coalescent.SmcBound.raceBound, ih, hazard_cast]

theorem harmonic_cast (m : Nat) :
    (harmonic m : Real) = Rhone.Coalescent.SmcBound.harmonic m := by
  induction m with
  | zero => simp [harmonic, Rhone.Coalescent.SmcBound.harmonic]
  | succ m ih => simp [harmonic, Rhone.Coalescent.SmcBound.harmonic, ih]

theorem doubleBound_cast (R : Rat) (m : Nat) :
    (doubleBound R m : Real) = Rhone.Coalescent.SmcBound.doubleBound (R : Real) m := by
  induction m with
  | zero => simp [doubleBound, Rhone.Coalescent.SmcBound.doubleBound]
  | succ m ih =>
    simp [doubleBound, Rhone.Coalescent.SmcBound.doubleBound, ih,
      hazard_cast, raceBound_cast]

theorem quadraticCoefficient_cast (m : Nat) :
    (quadraticCoefficient m : Real) = Rhone.Coalescent.SmcBound.quadraticCoefficient m := by
  induction m with
  | zero => simp [quadraticCoefficient, Rhone.Coalescent.SmcBound.quadraticCoefficient]
  | succ m ih =>
    simp [quadraticCoefficient, Rhone.Coalescent.SmcBound.quadraticCoefficient, ih,
      harmonic_cast]

theorem quadraticBound_cast (R : Rat) (m : Nat) :
    (quadraticBound R m : Real) =
      (R : Real) ^ 2 * Rhone.Coalescent.SmcBound.quadraticCoefficient m := by
  simp [quadraticBound, pow_two, quadraticCoefficient_cast]

theorem clippedQuadraticBound_cast (R : Rat) (m : Nat) :
    (clippedQuadraticBound R m : Real) =
      min 1 ((R : Real) ^ 2 * Rhone.Coalescent.SmcBound.quadraticCoefficient m) := by
  simp [clippedQuadraticBound, quadraticBound_cast]

end Rhone.Computation.SmcPrimeTv
