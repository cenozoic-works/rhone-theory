/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat
public import Init.Data.Array.OfFn

/-!
# Exact identity/reference-diversity values for the existing infinitely unrelated-pool sampling law
-/

@[expose] public section
namespace Rhone.Computation.IslandIdentity

def step (N : Nat) (m F : Rat) : Rat :=
  (1 - m) ^ 2 * (1 / (2 * N : Nat) + (1 - 1 / (2 * N : Nat)) * F)

def generation (N : Nat) (m : Rat) : Nat → Rat → Rat
  | 0, F => F
  | t + 1, F => step N m (generation N m t F)

def equilibrium (N : Nat) (m : Rat) : Rat :=
  (1 - m) ^ 2 / ((2 * N : Nat) - (1 - m) ^ 2 * ((2 * N : Nat) - 1))

def within (factor F : Rat) : Rat := factor * (1 - F)

def between (factor : Rat) : Rat := factor

def referenceRatio (factor F : Rat) : Rat := 1 - within factor F / between factor

def row (factor F : Rat) : Array Rat :=
  #[F, within factor F, between factor, referenceRatio factor F]

def values (N : Nat) (m F0 factor : Rat) (t : Nat) : Array (Array Rat) :=
  (Array.ofFn (fun i : Fin (t + 1) => row factor (generation N m i.val F0))).push
    (row factor (equilibrium N m))

def check (N : Nat) (m F0 factor : Rat) (t : Nat) (claim : Array (Array Rat)) : Bool :=
  decide (claim = values N m F0 factor t)

end Rhone.Computation.IslandIdentity
