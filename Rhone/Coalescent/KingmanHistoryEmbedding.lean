/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanForestEmbedding
public import Rhone.Combinatorics.KingmanHistoryPayoff
/-!
# Chronological Kingman histories commute with injective leaf-label embeddings

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def nextForestEmbedEquiv {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L)) :
    {G : Finset (Finset L) // G ∈ ADR11.merges F} ≃
      {H : Finset (Finset M) // H ∈ ADR11.merges (forestEmbed e F)} :=
  Equiv.ofBijective
    (fun G => ⟨forestEmbed e G.1, by
      rw [merges_forestEmbed]
      exact mem_image_of_mem _ G.2⟩)
    ⟨by
      intro G H he
      apply Subtype.ext
      exact forestEmbed_injective e (congrArg Subtype.val he),
    by
      intro H
      have hm : H.1 ∈ (ADR11.merges F).image (forestEmbed e) := by
        simpa only [merges_forestEmbed] using H.2
      obtain ⟨G, hG, he⟩ := mem_image.mp hm
      exact ⟨⟨G, hG⟩, Subtype.ext he⟩⟩
noncomputable def historyEmbedEquiv {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) :
    (t : ℕ) → Combinatorics.RankedForestHistory F t ≃ Combinatorics.RankedForestHistory
        (forestEmbed e F) t
  | 0 => Equiv.punitEquivPUnit
  | t + 1 => Equiv.sigmaCongr (nextForestEmbedEquiv e F)
      (fun G => historyEmbedEquiv e G.1 t)
theorem historyEnd_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L))
    (t : ℕ) (h : Combinatorics.RankedForestHistory F t) :
    Combinatorics.historyEnd (forestEmbed e F) t (historyEmbedEquiv e F t h) =
      forestEmbed e (Combinatorics.historyEnd F t h) := by
  induction t generalizing F with
  | zero => rfl
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    change Combinatorics.historyEnd (forestEmbed e G.1) t (historyEmbedEquiv e G.1 t h) =
      forestEmbed e (Combinatorics.historyEnd G.1 t h)
    exact ih G.1 h
theorem jumpMatrix_forestEmbed_merge {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F G : Finset (Finset L))
    (hG : G ∈ ADR11.merges F) :
    ADR11.jumpMatrix (forestEmbed e F) (forestEmbed e G) = ADR11.jumpMatrix F G := by
  obtain ⟨B, hB, C, hC, hBC, _⟩ := ADR11.mem_merges.mp hG
  have hsub : ({B, C} : Finset (Finset L)) ⊆ ADR11.roots F := by
    intro D hD
    rcases mem_insert.mp hD with rfl | hD
    · exact hB
    · exact mem_singleton.mp hD ▸ hC
  have hk : 2 ≤ (ADR11.roots F).card := by
    have hh := card_le_card hsub
    simpa only [card_pair hBC] using hh
  have hm : forestEmbed e G ∈ ADR11.merges (forestEmbed e F) := by
    rw [merges_forestEmbed]
    exact mem_image_of_mem _ hG
  rw [ADR11.jumpMatrix_apply_of_isForest (by rw [card_roots_forestEmbed]; exact hk),
    ADR11.jumpMatrix_apply_of_isForest hk, ite_eq_left hm, ite_eq_left hG, card_roots_forestEmbed]
theorem historyMass_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L))
    (t : ℕ) (h : Combinatorics.RankedForestHistory F t) :
    Combinatorics.historyMass (forestEmbed e F) t (historyEmbedEquiv e F t h) =
        Combinatorics.historyMass F t h := by
  induction t generalizing F with
  | zero => rfl
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    change ADR11.jumpMatrix (forestEmbed e F) (forestEmbed e G.1) *
      Combinatorics.historyMass (forestEmbed e G.1) t (historyEmbedEquiv e G.1 t h) =
        ADR11.jumpMatrix F G.1 * Combinatorics.historyMass G.1 t h
    rw [jumpMatrix_forestEmbed_merge e F G.1 G.2, ih G.1 h]
theorem historyPayoff_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L))
    (t : ℕ) (f : Finset (Finset M) → ℝ) :
    Combinatorics.historyPayoff (forestEmbed e F) t f = Combinatorics.historyPayoff F t
        (fun G => f (forestEmbed e G)) := by
  unfold Combinatorics.historyPayoff
  rw [← (historyEmbedEquiv e F t).sum_comp]
  simp_rw [historyEnd_forestEmbed, historyMass_forestEmbed]
end Rhone.Coalescent
