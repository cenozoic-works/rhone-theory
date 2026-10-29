/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanTopologyWeight

/-!
# Topology endpoint events split into the smaller history laws

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem history_payoff_topology_split (n : ℕ) (hn : 1 ≤ n)
    (T : Finset (Finset (Fin n))) (hT : ADR11.IsBinaryHierarchy T)
    (A : Finset (Fin n)) (hsT : ADR11.roots (T.erase univ) = {A, univ \ A}) :
    Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
        (fun G => if G = T then 1 else 0) =
      splitHistoryPayoff (ADR11.singletonForest n) A
        (fun G => if G = T.filter (fun C => C ⊆ A) then 1 else 0)
        (fun G => if G = T.filter (fun C => C ⊆ univ \ A) then 1 else 0) := by
  classical
  unfold splitHistoryPayoff
  rw [ADR11.card_roots_singletonForest]
  unfold Combinatorics.historyPayoff
  apply sum_congr rfl
  intro h hh
  let G := Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h
  have hG := Combinatorics.historyEnd_isBinaryHierarchy n hn h
  change Combinatorics.historyMass _ _ h * (if G = T then 1 else 0) =
    Combinatorics.historyMass _ _ h * (if ADR11.roots (G.erase univ) = {A, univ \ A} then
      (if G.filter (fun C => C ⊆ A) = T.filter (fun C => C ⊆ A) then 1 else 0) *
      (if G.filter (fun C => C ⊆ univ \ A) =
        T.filter (fun C => C ⊆ univ \ A) then 1 else 0) else 0)
  by_cases he : G = T
  · simp [he, hsT]
  · by_cases hs : ADR11.roots (G.erase univ) = {A, univ \ A}
    · by_cases ha : G.filter (fun C => C ⊆ A) = T.filter (fun C => C ⊆ A)
      · have hb : G.filter (fun C => C ⊆ univ \ A) ≠
          T.filter (fun C => C ⊆ univ \ A) := by
          intro hb
          exact he (root_split_endpoint_reconstruction G T A hG.1.1 hT.1.1 hs hsT ha hb)
        simp [he, hs, ha, hb]
      · simp [he, hs, ha]
    · simp [he, hs]

noncomputable def cladeLabelEmbedding {n : ℕ} (A : Finset (Fin n)) : Fin A.card ↪ Fin n :=
  A.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ A))

theorem cladeLabelEmbedding_range {n : ℕ} (A : Finset (Fin n)) :
    (univ : Finset (Fin A.card)).map (cladeLabelEmbedding A) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact (A.equivFin.symm y).2
  · intro hx
    refine mem_map.mpr ⟨A.equivFin ⟨x, hx⟩, mem_univ _, ?_⟩
    change (A.equivFin.symm (A.equivFin ⟨x, hx⟩)).val = x
    rw [Equiv.symm_apply_apply]

theorem topology_subtree_payoff (n a : ℕ) (G : Finset (Finset (Fin n)))
    (A : Finset (Fin n)) (e : Fin a ↪ Fin n)
    (he : (univ : Finset (Fin a)).map e = A) :
    Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ A)) (a - 1)
      (fun H => if H = G.filter (fun C => C ⊆ A) then 1 else 0) =
    Combinatorics.historyPayoff (ADR11.singletonForest a) (a - 1)
      (fun H => if H = forestPreimage e (G.filter (fun C => C ⊆ A)) then 1 else 0) := by
  classical
  have hback : forestEmbed e (forestPreimage e (G.filter (fun C => C ⊆ A))) =
      G.filter (fun C => C ⊆ A) := by
    apply forestEmbed_forestPreimage
    intro C hc
    rw [he]
    exact (mem_filter.mp hc).2
  rw [← he, ← singletonForest_forestEmbed, historyPayoff_forestEmbed]
  unfold Combinatorics.historyPayoff
  apply sum_congr rfl
  intro h hh
  congr 1
  have heq : forestEmbed e (Combinatorics.historyEnd (ADR11.singletonForest a) (a - 1) h) =
      G.filter (fun C => C ⊆ (univ : Finset (Fin a)).map e) ↔
      Combinatorics.historyEnd (ADR11.singletonForest a) (a - 1) h =
        forestPreimage e (G.filter (fun C => C ⊆ (univ : Finset (Fin a)).map e)) := by
    rw [he]
    constructor
    · intro hh
      exact forestEmbed_injective e (hh.trans hback.symm)
    · intro hh
      rw [hh, hback]
  simp only [heq]

theorem singleton_roots_within_count (n : ℕ) (A : Finset (Fin n)) :
    ((ADR11.roots (ADR11.singletonForest n)).filter (fun C => C ⊆ A)).card = A.card := by
  classical
  rw [ADR11.roots_singletonForest]
  have he : (ADR11.singletonForest n).filter (fun C => C ⊆ A) =
      A.image (fun x => {x}) := by
    ext C
    simp only [ADR11.singletonForest, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, singleton_subset_iff.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, singleton_subset_iff.mpr hx⟩
  rw [he, card_image_of_injective _ (fun _ _ h => singleton_injective h)]

theorem topologyWeight_root_split (n : ℕ) (hn : 2 ≤ n) (T : LabelledTopology n)
    (A : Finset (Fin n)) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hs : ADR11.roots (T.1.erase univ) = {A, univ \ A}) :
    topologyWeight n T = (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) *
      Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ A)) (A.card - 1)
        (fun G => if G = T.1.filter (fun C => C ⊆ A) then 1 else 0) *
      Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ univ \ A))
        ((univ \ A).card - 1)
        (fun G => if G = T.1.filter (fun C => C ⊆ univ \ A) then 1 else 0) := by
  classical
  have hpure : ∀ C ∈ ADR11.singletonForest n, C ⊆ A ∨ C ⊆ univ \ A := by
    intro C hc
    obtain ⟨x, _, rfl⟩ := mem_image.mp hc
    by_cases hx : x ∈ A
    · exact Or.inl (singleton_subset_iff.mpr hx)
    · exact Or.inr (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _, hx⟩))
  have hr : pureRootSplitPayoff (ADR11.singletonForest n) A = rootSplitMass n A := by
    unfold pureRootSplitPayoff rootSplitMass Combinatorics.historyPayoff
    rw [ADR11.card_roots_singletonForest]
    apply sum_congr rfl
    intro h hh
    split_ifs <;> simp_all
  have hAn : A.card < n := by
    have hc := card_sdiff_of_subset (subset_univ A)
    rw [card_univ, Fintype.card_fin] at hc
    have hp := card_pos.mpr hAc
    omega
  unfold topologyWeight
  rw [history_payoff_topology_split n (by omega) T.1 T.2 A hs,
    split_history_payoff_factorization _ (ADR11.isForest_singletonForest n) A hA hAc
      (ADR11.absorb_lineages_singletonForest n) hpure,
    singleton_roots_within_count, singleton_roots_within_count, hr,
    root_split_mass n hn A (card_pos.mpr hA) hAn]
end Rhone.Coalescent
