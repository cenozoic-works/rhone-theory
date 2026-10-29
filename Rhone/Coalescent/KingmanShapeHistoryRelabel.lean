/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanHistoryEmbeddingRanks
public import Rhone.Combinatorics.KingmanShapeHistoryTrace
/-!
# Leaf permutations act on complete chronological merger histories

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_castForest {L : Type*} [Fintype L] [DecidableEq L]
    (F H : Finset (Finset L)) (he : F = H) (t : ℕ)
    (h : Combinatorics.RankedForestHistory F t) (k : ℕ) :
    Combinatorics.historyAt H t
        (Equiv.cast (congrArg (fun W => Combinatorics.RankedForestHistory W t) he) h) k =
      Combinatorics.historyAt F t h k := by
  subst H
  rfl
noncomputable def historyRelabel {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (e : Equiv.Perm L)
    (he : forestEmbed e.toEmbedding F = F) :
    Combinatorics.RankedForestHistory F t ≃ Combinatorics.RankedForestHistory F t :=
  (historyEmbedEquiv e.toEmbedding F t).trans
    (Equiv.cast (congrArg (fun W => Combinatorics.RankedForestHistory W t) he))
theorem historyAt_historyRelabel {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (e : Equiv.Perm L)
    (he : forestEmbed e.toEmbedding F = F) (h : Combinatorics.RankedForestHistory F t) (k : ℕ) :
    Combinatorics.historyAt F t (historyRelabel F t e he h) k =
      Combinatorics.forestRelabel e (Combinatorics.historyAt F t h k) := by
  exact (historyAt_castForest _ _ he t (historyEmbedEquiv e.toEmbedding F t h) k).trans
    (historyAt_forestEmbed e.toEmbedding F t h k)
theorem forestEmbed_singletonForest_perm (n : ℕ) (e : Equiv.Perm (Fin n)) :
    forestEmbed e.toEmbedding (ADR11.singletonForest n) = ADR11.singletonForest n := by
  ext C
  constructor
  · intro hC
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hA
    exact mem_image.mpr ⟨e x, mem_univ _, (map_singleton e.toEmbedding x).symm⟩
  · intro hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    exact mem_image.mpr ⟨{e.symm x}, mem_image.mpr ⟨e.symm x, mem_univ _, rfl⟩,
      by
        rw [map_singleton]
        change {e (e.symm x)} = {x}
        rw [Equiv.apply_symm_apply]⟩
theorem rankedShapeRel_iff_historyRelabel (n : ℕ) (h h' : Combinatorics.RankedLabelledHistory n) :
    Combinatorics.RankedShapeRel n h h' ↔ ∃ e : Equiv.Perm (Fin n),
      historyRelabel (ADR11.singletonForest n) (n - 1) e
        (forestEmbed_singletonForest_perm n e) h = h' := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, Combinatorics.historyAt_history_ext _ _ _ _ ?_⟩
    intro k hk
    rw [historyAt_historyRelabel]
    exact he k hk
  · rintro ⟨e, rfl⟩
    exact ⟨e, fun k _ => (historyAt_historyRelabel _ _ _ _ _ k).symm⟩
end Rhone.Coalescent
