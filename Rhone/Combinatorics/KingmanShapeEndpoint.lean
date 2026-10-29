/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeEndpointStep
/-! # Every binary hierarchy is the endpoint of a ranked Kingman merger history -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem historyEnd_complete_binary {L : Type*} [Fintype L] [DecidableEq L]
    (F G : Finset (Finset L)) (hF : ADR11.IsForest F)
    (hG : ADR11.IsBinaryHierarchy G) (hFG : F ⊆ G)
    (hsingle : ∀ x : L, {x} ∈ F)
    (hdown : ∀ A ∈ F, ∀ B ∈ G, B ⊆ A → B ∈ F) :
    ∃ h : RankedForestHistory F (G.card - F.card),
      historyEnd F (G.card - F.card) h = G := by
  classical
  have complete (t : ℕ) : ∀ (F : Finset (Finset L)), ADR11.IsForest F → F ⊆ G →
      (∀ x : L, {x} ∈ F) →
      (∀ A ∈ F, ∀ B ∈ G, B ⊆ A → B ∈ F) → G.card - F.card = t →
      ∃ h : RankedForestHistory F t, historyEnd F t h = G := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro F hF hFG hsingle hdown ht
      by_cases he : F = G
      · subst F
        have ht0 : t = 0 := by omega
        rw [ht0]
        exact ⟨PUnit.unit, rfl⟩
      · obtain ⟨A, hAG, hAF, hproper, hm⟩ :=
          binaryHierarchy_missing_merge F G hG hFG he hsingle hdown
        have hFGc : F.card < G.card :=
          card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFG, he⟩)
        have hnew : (insert A F).card = F.card + 1 := card_insert_of_notMem hAF
        have hlt : G.card - (insert A F).card < t := by omega
        have hsub : insert A F ⊆ G := insert_subset hAG hFG
        have hsingle' : ∀ x : L, {x} ∈ insert A F :=
          fun x => mem_insert_of_mem (hsingle x)
        have hdown' : ∀ C ∈ insert A F, ∀ B ∈ G, B ⊆ C → B ∈ insert A F := by
          intro C hC B hBG hBC
          rcases mem_insert.mp hC with hCA | hCF
          · rw [hCA] at hBC
            by_cases heBA : B = A
            · exact mem_insert.mpr (Or.inl heBA)
            · exact mem_insert_of_mem
                (hproper B hBG (Finset.ssubset_iff_subset_ne.mpr ⟨hBC, heBA⟩))
          · exact mem_insert_of_mem (hdown C hCF B hBG hBC)
        obtain ⟨tail, htail⟩ := ih (G.card - (insert A F).card) hlt (insert A F)
          (hF.of_mem_merges hm).1 hsub hsingle' hdown' rfl
        have hlen : t = G.card - (insert A F).card + 1 := by omega
        rw [hlen]
        exact ⟨⟨⟨insert A F, hm⟩, tail⟩, htail⟩
  exact complete (G.card - F.card) F hF hFG hsingle hdown rfl
theorem historyEnd_surjective_binary (n : ℕ) (hn : 1 ≤ n)
    (G : Finset (Finset (Fin n))) (hG : ADR11.IsBinaryHierarchy G) :
    ∃ h : RankedLabelledHistory n,
      historyEnd (ADR11.singletonForest n) (n - 1) h = G := by
  classical
  have hsub : ADR11.singletonForest n ⊆ G := by
    intro C hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    exact hG.1.2.1 x
  have hsingle : ∀ x : Fin n, {x} ∈ ADR11.singletonForest n := by
    intro x
    simp [ADR11.singletonForest]
  have hdown : ∀ A ∈ ADR11.singletonForest n, ∀ B ∈ G, B ⊆ A →
      B ∈ ADR11.singletonForest n := by
    intro A hA B hBG hBA
    obtain ⟨x, _, rfl⟩ := mem_image.mp hA
    have he : B = {x} := (subset_singleton_iff.mp hBA).resolve_left
      (hG.1.2.2.1 B hBG).ne_empty
    rw [he]
    exact hsingle x
  have hcard : (ADR11.singletonForest n).card = n := by
    simp only [ADR11.singletonForest, card_image_of_injective _ singleton_injective,
      card_univ, Fintype.card_fin]
  have hlen : G.card - (ADR11.singletonForest n).card = n - 1 := by
    rw [ADR11.counts_card_eq hG, Fintype.card_fin, hcard]
    omega
  have hh := historyEnd_complete_binary (ADR11.singletonForest n) G
    (ADR11.isForest_singletonForest n) hG hsub hsingle hdown
  exact Eq.mp (congrArg (fun t => ∃ h : RankedForestHistory (ADR11.singletonForest n) t,
    historyEnd (ADR11.singletonForest n) t h = G) hlen) hh
end Rhone.Combinatorics
