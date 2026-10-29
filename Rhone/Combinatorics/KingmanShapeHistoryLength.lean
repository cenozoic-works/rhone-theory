/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapes
/-! # Casting a ranked history along equal lengths preserves its forests and endpoint -/
@[expose] public section
namespace Rhone.Combinatorics
theorem historyAt_castLength {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t u : ℕ) (he : t = u)
    (h : RankedForestHistory F t) (k : ℕ) :
    historyAt F u (Equiv.cast (congrArg (RankedForestHistory F) he) h) k =
      historyAt F t h k := by
  subst u
  rfl
theorem historyEnd_castLength {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t u : ℕ) (he : t = u) (h : RankedForestHistory F t) :
    historyEnd F u (Equiv.cast (congrArg (RankedForestHistory F) he) h) = historyEnd F t h := by
  subst u
  rfl
end Rhone.Combinatorics
