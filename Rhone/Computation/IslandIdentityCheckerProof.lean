/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.IslandIdentity

/-! # Typed exact acceptance covers every ordered scalar and complete array shape -/

@[expose] public section
namespace Rhone.Computation.IslandIdentity

theorem check_iff (N : Nat) (m F0 factor : Rat) (t : Nat) (claim : Array (Array Rat)) :
    check N m F0 factor t claim = true ↔ claim = values N m F0 factor t := by
  simp [check]

theorem check_complete (N : Nat) (m F0 factor : Rat) (t : Nat) :
    check N m F0 factor t (values N m F0 factor t) = true := by
  simp [check]

end Rhone.Computation.IslandIdentity
