/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryInterleave
/-! # Truncate histories while retaining their exact chronological forests -/
@[expose] public section
namespace Rhone.Coalescent
noncomputable def historyTake {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : Combinatorics.RankedForestHistory F t)
    (r : ℕ) (hr : r ≤ t) : Combinatorics.RankedForestHistory F r :=
  (Combinatorics.rankedForestHistoryTraceEquiv F r).symm
    ⟨fun k => Combinatorics.historyAt F t h k.val, Combinatorics.historyAt_zero F t h,
      fun k => Combinatorics.historyAt_next_merge F t h k.val (by have := k.isLt; omega)⟩
theorem historyAt_historyTake {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : Combinatorics.RankedForestHistory F t)
    (r : ℕ) (hr : r ≤ t) (k : ℕ) (hk : k ≤ r) :
    Combinatorics.historyAt F r (historyTake F t h r hr) k = Combinatorics.historyAt F t h k := by
  have he := (Combinatorics.rankedForestHistoryTraceEquiv F r).apply_symm_apply
    (⟨fun k => Combinatorics.historyAt F t h k.val, Combinatorics.historyAt_zero F t h,
      fun k => Combinatorics.historyAt_next_merge F t h k.val (by have := k.isLt; omega)⟩ :
      Combinatorics.ForestMergerTrace F r)
  exact congrFun (congrArg Subtype.val he) ⟨k, by omega⟩
theorem historyEnd_historyTake {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : Combinatorics.RankedForestHistory F t)
    (r : ℕ) (hr : r ≤ t) :
    Combinatorics.historyEnd F r (historyTake F t h r hr) = Combinatorics.historyAt F t h r := by
  rw [← historyAt_terminal, historyAt_historyTake F t h r hr r le_rfl]
end Rhone.Coalescent
