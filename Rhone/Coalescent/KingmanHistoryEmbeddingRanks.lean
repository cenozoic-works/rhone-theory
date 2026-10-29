/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanHistoryEmbedding
public import Rhone.Combinatorics.KingmanShapes
/-!
# Every chronological forest is preserved by history leaf-label embedding

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
theorem historyAt_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L))
    (t : ℕ) (h : Combinatorics.RankedForestHistory F t) (k : ℕ) :
    Combinatorics.historyAt (forestEmbed e F) t (historyEmbedEquiv e F t h) k =
      forestEmbed e (Combinatorics.historyAt F t h k) := by
  induction t generalizing F k with
  | zero => rfl
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    cases k with
    | zero => rfl
    | succ k =>
      change Combinatorics.historyAt (forestEmbed e G.1) t (historyEmbedEquiv e G.1 t h) k =
        forestEmbed e (Combinatorics.historyAt G.1 t h k)
      exact ih G.1 h k
end Rhone.Coalescent
