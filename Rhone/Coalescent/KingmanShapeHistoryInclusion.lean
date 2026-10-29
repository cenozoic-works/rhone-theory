/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryTake
public import Rhone.Combinatorics.KingmanHistoryTopology
/-! # Chronological merger histories retain every previously formed clade -/
@[expose] public section
namespace Rhone.Coalescent
theorem historyAt_subset_historyEnd {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : Combinatorics.RankedForestHistory F t) (k : ℕ) (hk : k ≤ t) :
    Combinatorics.historyAt F t h k ⊆ Combinatorics.historyEnd F t h := by
  induction t generalizing F k with
  | zero => exact subset_rfl
  | succ t ih =>
    cases k with
    | zero => exact (Combinatorics.historyEnd_spec F hF (t+1) h).2.2.1
    | succ k => exact ih h.1.1 (hF.of_mem_merges h.1.2).1 h.2 k (by omega)
theorem historyAt_subset {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : Combinatorics.RankedForestHistory F t) (k l : ℕ) (hkl : k ≤ l) (hlt : l ≤ t) :
    Combinatorics.historyAt F t h k ⊆ Combinatorics.historyAt F t h l := by
  have hs := historyAt_subset_historyEnd F hF l (historyTake F t h l hlt) k hkl
  rwa [historyAt_historyTake, historyEnd_historyTake] at hs
end Rhone.Coalescent
