/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootOrientation
public import Rhone.Coalescent.KingmanForestEmbedding
public import Mathlib.NumberTheory.Harmonic.Defs
/-!
# Colless' statistic on retained binary genealogy clades

Source: cardona2013balance, §7. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
noncomputable def treeColless {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) : ℕ :=
  ∑ C ∈ G.filter (fun C => 2 ≤ C.card),
    let m := (ADR11.roots ((G.filter (fun D => D ⊆ C)).erase C)).sup Finset.card
    m - (C.card - m)
/-- Source: cardona2013balance, §7. -/
noncomputable def cladeColless {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (C : Finset L) : ℕ :=
  let m := (ADR11.roots ((G.filter (fun D => D ⊆ C)).erase C)).sup Finset.card
  m - (C.card - m)
/-- Source: cardona2013balance, §7. -/
theorem cladeColless_filter {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (A C : Finset L) (hCA : C ⊆ A) :
    cladeColless (G.filter (fun D => D ⊆ A)) C = cladeColless G C := by
  have he : (G.filter (fun D => D ⊆ A)).filter (fun D => D ⊆ C) =
      G.filter (fun D => D ⊆ C) := by
    ext D
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hCA⟩, h.2⟩⟩
  simp only [cladeColless, he]
/-- Source: cardona2013balance, §7. -/
theorem cladeColless_univ {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) :
    cladeColless G univ =
      let m := (ADR11.roots (G.erase univ)).sup Finset.card
      m - (Fintype.card L - m) := by
  have he : G.filter (fun D => D ⊆ univ) = G := by simp
  simp only [cladeColless, he, card_univ]
/-- Source: cardona2013balance, §7. -/
theorem treeColless_root_split {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G)
    (A : Finset L) (hA : A.Nonempty) (hB : (univ \ A).Nonempty)
    (hs : ADR11.roots (G.erase univ) = {A, univ \ A}) :
    treeColless G = treeColless (G.filter (fun C => C ⊆ A)) +
      treeColless (G.filter (fun C => C ⊆ univ \ A)) +
      (max A.card (univ \ A).card - min A.card (univ \ A).card) := by
  let S := G.filter (fun C => 2 ≤ C.card)
  let SA := S.filter (fun C => C ⊆ A)
  let SB := S.filter (fun C => C ⊆ univ \ A)
  have hd : Disjoint A (univ \ A) := disjoint_sdiff_self_right
  have haU : ¬univ ⊆ A := by
    obtain ⟨x, hx⟩ := hB
    exact fun h => (mem_sdiff.mp hx).2 (h (mem_univ x))
  have hbU : ¬univ ⊆ univ \ A := by
    obtain ⟨x, hx⟩ := hA
    exact fun h => (mem_sdiff.mp (h (mem_univ x))).2 hx
  have hcard : Fintype.card L = A.card + (univ \ A).card := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ]
    have hle := card_le_card (subset_univ A)
    rw [card_univ] at hle
    omega
  have hL : 2 ≤ Fintype.card L := by
    have hca := card_pos.mpr hA
    have hcb := card_pos.mpr hB
    omega
  have hdis : Disjoint SA SB := by
    apply disjoint_left.mpr
    intro C hca hcb
    have hCG := (mem_filter.mp (mem_filter.mp hca).1).1
    obtain ⟨x, hx⟩ := hG.1.2.2.1 C hCG
    exact disjoint_left.mp hd ((mem_filter.mp hca).2 hx) ((mem_filter.mp hcb).2 hx)
  have hUn : univ ∉ SA ∪ SB := by
    simp only [mem_union, mem_filter, SA, SB]
    exact fun h => h.elim (fun h => haU h.2) (fun h => hbU h.2)
  have hpart : S = insert univ (SA ∪ SB) := by
    ext C
    constructor
    · intro hc
      obtain ⟨hcG, hc2⟩ := mem_filter.mp hc
      rcases Combinatorics.root_split_clade_purity G A hs C hcG with rfl | hcA | hcB
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hc, hcA⟩))
      · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hc, hcB⟩))
    · intro hc
      rcases mem_insert.mp hc with rfl | hc
      · exact mem_filter.mpr ⟨hG.1.1, by simpa using hL⟩
      · exact (mem_union.mp hc).elim (fun h => (mem_filter.mp h).1)
          (fun h => (mem_filter.mp h).1)
  have hleft : treeColless (G.filter (fun C => C ⊆ A)) =
      ∑ C ∈ SA, cladeColless G C := by
    unfold treeColless
    have he : (G.filter (fun C => C ⊆ A)).filter (fun C => 2 ≤ C.card) = SA := by
      ext C
      simp only [SA, S, mem_filter]
      tauto
    rw [he]
    apply sum_congr rfl
    intro C hc
    exact cladeColless_filter G A C (mem_filter.mp hc).2
  have hright : treeColless (G.filter (fun C => C ⊆ univ \ A)) =
      ∑ C ∈ SB, cladeColless G C := by
    unfold treeColless
    have he : (G.filter (fun C => C ⊆ univ \ A)).filter (fun C => 2 ≤ C.card) = SB := by
      ext C
      simp only [SB, S, mem_filter]
      tauto
    rw [he]
    apply sum_congr rfl
    intro C hc
    exact cladeColless_filter G (univ \ A) C (mem_filter.mp hc).2
  have hroot : cladeColless G univ =
      max A.card (univ \ A).card - min A.card (univ \ A).card := by
    rw [cladeColless_univ, hs]
    simp only [sup_insert, sup_singleton, hcard]
    change max A.card (univ \ A).card -
      (A.card + (univ \ A).card - max A.card (univ \ A).card) = _
    rcases le_total A.card (univ \ A).card with h | h
    · rw [max_eq_right h, min_eq_left h]
      omega
    · rw [max_eq_left h, min_eq_right h]
      omega
  change (∑ C ∈ S, cladeColless G C) = _
  rw [hpart, sum_insert hUn, sum_union hdis, hleft, hright, hroot]
  omega
/-- Source: cardona2013balance, §7. -/
theorem cladeColless_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (G : Finset (Finset L))
    (C : Finset L) : cladeColless (forestEmbed e G) (C.map e) = cladeColless G C := by
  have hf : (forestEmbed e G).filter (fun D => D ⊆ C.map e) =
      forestEmbed e (G.filter (fun D => D ⊆ C)) := by
    ext D
    constructor
    · intro hD
      obtain ⟨hDG, hDC⟩ := mem_filter.mp hD
      obtain ⟨E, hE, rfl⟩ := mem_image.mp hDG
      exact mem_image.mpr ⟨E, mem_filter.mpr ⟨hE, map_subset_map.mp hDC⟩, rfl⟩
    · intro hD
      obtain ⟨E, hE, rfl⟩ := mem_image.mp hD
      obtain ⟨hEG, hEC⟩ := mem_filter.mp hE
      exact mem_filter.mpr ⟨mem_image.mpr ⟨E, hEG, rfl⟩, map_subset_map.mpr hEC⟩
  have he : (forestEmbed e (G.filter (fun D => D ⊆ C))).erase (C.map e) =
      forestEmbed e ((G.filter (fun D => D ⊆ C)).erase C) :=
    (image_erase (map_injective e) _ _).symm
  unfold cladeColless
  rw [hf, he, roots_forestEmbed]
  simp only [forestEmbed, sup_image, Function.comp_def, card_map]
/-- Source: cardona2013balance, §7. -/
theorem treeColless_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (G : Finset (Finset L)) :
    treeColless (forestEmbed e G) = treeColless G := by
  have hf : (forestEmbed e G).filter (fun C => 2 ≤ C.card) =
      forestEmbed e (G.filter (fun C => 2 ≤ C.card)) := by
    ext C
    constructor
    · intro hc
      obtain ⟨hcG, hc2⟩ := mem_filter.mp hc
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hcG
      exact mem_image.mpr ⟨D, mem_filter.mpr ⟨hD, by simpa using hc2⟩, rfl⟩
    · intro hc
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hc
      exact mem_filter.mpr ⟨mem_image.mpr ⟨D, (mem_filter.mp hD).1, rfl⟩,
        by simpa using (mem_filter.mp hD).2⟩
  change (∑ C ∈ (forestEmbed e G).filter (fun C => 2 ≤ C.card),
    cladeColless (forestEmbed e G) C) = ∑ C ∈ G.filter (fun C => 2 ≤ C.card), cladeColless G C
  rw [hf]
  unfold forestEmbed
  rw [sum_image (fun C _ D _ h => map_injective e h)]
  apply sum_congr rfl
  intro C hc
  exact cladeColless_forestEmbed e G C
/-- Source: cardona2013balance, §7. -/
theorem treeColless_singletonForest (n : ℕ) : treeColless (ADR11.singletonForest n) = 0 := by
  have he : (ADR11.singletonForest n).filter (fun C => 2 ≤ C.card) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro C hc
    obtain ⟨hc, hc2⟩ := mem_filter.mp hc
    obtain ⟨x, _, rfl⟩ := mem_image.mp hc
    simp only [card_singleton] at hc2
    omega
  simp only [treeColless, he, sum_empty]
/-- Source: cardona2013balance, §7. -/
theorem kingman_colless_expectation_one :
    Combinatorics.historyPayoff (ADR11.singletonForest 1) 0 (fun G => (treeColless G : ℝ)) = 0 := by
  unfold Combinatorics.historyPayoff
  change (∑ _ : PUnit, 1 * (treeColless (ADR11.singletonForest 1) : ℝ)) = 0
  simp only [treeColless_singletonForest, Nat.cast_zero, mul_zero, sum_const_zero]
end Rhone.Coalescent
