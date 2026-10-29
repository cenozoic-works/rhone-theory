/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootAssemblyRoot
/-!
# Root assembly descends under the daughter ranked-shape relations

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
private theorem forestEmbed_sumCongr {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : Equiv.Perm L) (f : Equiv.Perm M)
    (F : Finset (Finset L)) (G : Finset (Finset M)) :
    forestEmbed (Equiv.sumCongr e f).toEmbedding
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr G) =
    forestEmbed Function.Embedding.inl (forestEmbed e.toEmbedding F) ∪
      forestEmbed Function.Embedding.inr (forestEmbed f.toEmbedding G) := by
  rw [forestEmbed_union, forestEmbed_comp, forestEmbed_comp,
    forestEmbed_comp, forestEmbed_comp]
  have hl : Function.Embedding.inl.trans (Equiv.sumCongr e f).toEmbedding =
      e.toEmbedding.trans Function.Embedding.inl := Function.Embedding.ext (fun _ => rfl)
  have hr : Function.Embedding.inr.trans (Equiv.sumCongr e f).toEmbedding =
      f.toEmbedding.trans Function.Embedding.inr := Function.Embedding.ext (fun _ => rfl)
  rw [hl, hr]
private theorem forestEmbed_conjugate {L M : Type*} [DecidableEq L] [DecidableEq M]
    (u : L ≃ M) (e : Equiv.Perm L) (F : Finset (Finset L)) :
    forestEmbed (u.symm.trans (e.trans u)).toEmbedding (forestEmbed u.toEmbedding F) =
      forestEmbed u.toEmbedding (forestEmbed e.toEmbedding F) := by
  rw [forestEmbed_comp, forestEmbed_comp]
  congr 1
  apply Function.Embedding.ext
  intro x
  change u (e (u.symm (u x))) = u (e x)
  rw [u.symm_apply_apply]
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem firstRootHistoryAssemble_shape_rel (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (h h' : Combinatorics.RankedLabelledHistory k.val)
        (g g' : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (hh : Combinatorics.RankedShapeRel k.val h h')
        (hg : Combinatorics.RankedShapeRel (n - k.val) g g') :
    Combinatorics.RankedShapeRel n (firstRootHistoryAssemble n hn k h g s)
      (firstRootHistoryAssemble n hn k h' g' s) := by
  obtain ⟨e, he⟩ := hh
  obtain ⟨f, hf⟩ := hg
  let u := firstRootAssemblyLabels n k
  let q := u.symm.trans ((Equiv.sumCongr e f).trans u)
  refine ⟨q, ?_⟩
  intro r hr
  change forestEmbed q.toEmbedding _ = _
  by_cases hr' : r ≤ n - 2
  · rw [historyAt_firstRootHistoryAssemble _ _ _ _ _ _ _ hr',
      historyAt_firstRootHistoryAssemble _ _ _ _ _ _ _ hr']
    rw [forestEmbed_conjugate, forestEmbed_sumCongr]
    change forestEmbed u.toEmbedding
      (forestEmbed Function.Embedding.inl
          (Combinatorics.forestRelabel e (Combinatorics.historyAt _ _ h _)) ∪
        forestEmbed Function.Embedding.inr
            (Combinatorics.forestRelabel f (Combinatorics.historyAt _ _ g _))) = _
    rw [he _ (Combinatorics.interleavingLeft_le s.1 r), hf _
        (Combinatorics.interleavingRight_le s.1 r)]
  · have hrend : r = n - 1 := by omega
    subst r
    rw [historyAt_terminal, historyAt_terminal,
      historyEnd_firstRootHistoryAssemble, historyEnd_firstRootHistoryAssemble,
      forestEmbed_conjugate]
    have hhe := he (k.val - 1) le_rfl
    have hfe := hf (n - k.val - 1) le_rfl
    rw [historyAt_terminal, historyAt_terminal] at hhe hfe
    unfold binaryHierarchyJoin
    simp only [forestEmbed, image_insert]
    rw [clade_map_equiv_univ]
    congr 1
    change forestEmbed u.toEmbedding
      (forestEmbed (Equiv.sumCongr e f).toEmbedding
        (forestEmbed Function.Embedding.inl (Combinatorics.historyEnd _ _ h) ∪
          forestEmbed Function.Embedding.inr (Combinatorics.historyEnd _ _ g))) = _
    rw [forestEmbed_sumCongr]
    change forestEmbed u.toEmbedding
      (forestEmbed Function.Embedding.inl
          (Combinatorics.forestRelabel e (Combinatorics.historyEnd _ _ h)) ∪
        forestEmbed Function.Embedding.inr
            (Combinatorics.forestRelabel f (Combinatorics.historyEnd _ _ g))) = _
    rw [hhe, hfe]
    rfl
end Rhone.Coalescent
