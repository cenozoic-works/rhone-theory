/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.IslandIdentity
public import Rhone.Statistics.IslandSampling

/-! # The rational evaluator equals the existing finite sampling law and recurrence -/

@[expose] public section
namespace Rhone.Computation.IslandIdentity

theorem step_cast (N : Nat) (m F : Rat) :
    (step N m F : Real) = Rhone.Dynamics.ibdStep (2 * N) m F := by
  simp [step, Rhone.Dynamics.ibdStep]

theorem step_eq_identityMass (N : Nat) (hN : 0 < N) (m F : Rat) :
    (step N m F : Real) = Rhone.Statistics.IslandIdentity.islandIdentityMass N m F := by
  rw [Rhone.Statistics.IslandIdentity.island_identity_mass_eq hN, step_cast]

theorem generation_cast (N : Nat) (m F0 : Rat) (t : Nat) :
    (generation N m t F0 : Real) = Rhone.Dynamics.ibdIter (2 * N) m t F0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [generation, Rhone.Dynamics.ibdIter, step_cast, ih]

theorem equilibrium_cast (N : Nat) (m : Rat) :
    (equilibrium N m : Real) = Rhone.Dynamics.ibdFixed (2 * N) m := by
  simp [equilibrium, Rhone.Dynamics.ibdFixed]

end Rhone.Computation.IslandIdentity
