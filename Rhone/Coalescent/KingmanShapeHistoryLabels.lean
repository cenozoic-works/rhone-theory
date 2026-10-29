/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryRelabel
/-!
# Chronological histories transport along derived bijective leaf labels

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
noncomputable def historyLabelsEquiv {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ≃ M)
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hFH : forestEmbed e.toEmbedding F = H)
    (t : ℕ) : Combinatorics.RankedForestHistory F t ≃ Combinatorics.RankedForestHistory H t :=
  (historyEmbedEquiv e.toEmbedding F t).trans
    (Equiv.cast (congrArg (fun W => Combinatorics.RankedForestHistory W t) hFH))
theorem historyAt_historyLabelsEquiv {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ≃ M)
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hFH : forestEmbed e.toEmbedding F = H)
    (t : ℕ) (h : Combinatorics.RankedForestHistory F t) (k : ℕ) :
    Combinatorics.historyAt H t (historyLabelsEquiv e F H hFH t h) k =
      forestEmbed e.toEmbedding (Combinatorics.historyAt F t h k) :=
  (historyAt_castForest _ _ hFH t (historyEmbedEquiv e.toEmbedding F t h) k).trans
    (historyAt_forestEmbed e.toEmbedding F t h k)
theorem historyAt_historyLabelsEquiv_symm {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ≃ M)
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hFH : forestEmbed e.toEmbedding F = H)
    (t : ℕ) (h : Combinatorics.RankedForestHistory H t) (k : ℕ) :
    forestEmbed e.toEmbedding
        (Combinatorics.historyAt F t ((historyLabelsEquiv e F H hFH t).symm h) k) =
      Combinatorics.historyAt H t h k := by
  have he := historyAt_historyLabelsEquiv e F H hFH t
    ((historyLabelsEquiv e F H hFH t).symm h) k
  rw [Equiv.apply_symm_apply] at he
  exact he.symm
end Rhone.Coalescent
