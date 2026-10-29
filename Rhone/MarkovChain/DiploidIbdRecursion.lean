/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.InbreedingEffectiveSampling

/-!
# Diploid identity-by-descent recursion from copy sampling

Source: crow_kimura1970, sec. 3.11; wright1931, p. 108. -/

@[expose] public section
namespace Rhone.MarkovChain.EffectiveSize

theorem diploid_offspring_ibd_recursion {A : Type*} [DecidableEq A]
    (N : Nat) (hN : 0 < N) (g : Fin (2 * N) → A) :
    offspringCopyIbd (2 * N) g = 1 / (2 * (N : Real)) +
      (1 - 1 / (2 * (N : Real))) * distinctCopyIbd (2 * N) g := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    offspring_copy_ibd_recursion (2 * N) (by omega) g

end Rhone.MarkovChain.EffectiveSize
