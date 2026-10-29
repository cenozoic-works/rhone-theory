/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSplitBase
public import Rhone.Coalescent.KingmanRootSplitAlgebra
/-! # First-merger decomposition of the two-colour root-split payoff -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem mixed_split_history_payoff_zero
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ) (A C : Finset L)
    (hC : C ∈ F) (hCu : C ≠ univ) (hCA : ¬C ⊆ A) (hCB : ¬C ⊆ univ \ A) :
    Combinatorics.historyPayoff F t
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then 1 else 0) = 0 := by
  unfold Combinatorics.historyPayoff
  apply sum_eq_zero
  intro h hh
  change Combinatorics.historyMass F t h *
      (if ADR11.roots ((Combinatorics.historyEnd F t h).erase univ) =
    {A, univ \ A} then 1 else 0) = 0
  rw [ite_eq_right (Combinatorics.root_split_excludes_mixed_history F hF t h A C hC hCu hCA hCB),
      mul_zero]
private theorem new_clade_within_iff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A B C : Finset L)
    (hB : B ∈ ADR11.roots F) (hC : C ∈ ADR11.roots F) (hBC : B ≠ C) :
    (∀ D ∈ insert (B ∪ C) F \ F, D ⊆ A) ↔ B ∪ C ⊆ A := by
  have hU := ADR11.union_not_mem_of_mem_roots hB hC hBC
  constructor
  · intro h
    exact h _ (mem_sdiff.mpr ⟨mem_insert_self _ _, hU⟩)
  · intro h D hD
    obtain ⟨hD, hn⟩ := mem_sdiff.mp hD
    rcases mem_insert.mp hD with rfl | hD
    · exact h
    · exact (hn hD).elim
private theorem not_subset_complement {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A B : Finset L)
    (hB : B ∈ ADR11.roots F) (hBA : B ⊆ A) : ¬B ⊆ univ \ A := by
  intro h
  obtain ⟨x, hx⟩ := hF.1 B (ADR11.roots_subset F hB)
  exact (mem_sdiff.mp (h hx)).2 (hBA hx)
private theorem not_subset_original {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A B : Finset L)
    (hB : B ∈ ADR11.roots F) (hBA : B ⊆ univ \ A) : ¬B ⊆ A := by
  intro h
  obtain ⟨x, hx⟩ := hF.1 B (ADR11.roots_subset F hB)
  exact (mem_sdiff.mp (hBA hx)).2 (h hx)
private theorem pure_after_insert {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A U : Finset L)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hU : U ⊆ A ∨ U ⊆ univ \ A) :
    ∀ C ∈ insert U F, C ⊆ A ∨ C ⊆ univ \ A := by
  intro C hC
  rcases mem_insert.mp hC with rfl | hC
  · exact hU
  · exact hpure C hC
theorem pure_root_split_history_step
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hk : 3 ≤ (ADR11.roots F).card)
    (hnext : ∀ G ∈ ADR11.merges F,
      (∀ C ∈ G, C ⊆ A ∨ C ⊆ univ \ A) →
      pureRootSplitPayoff G A =
        rootSplitValue (((ADR11.roots G).filter (fun C => C ⊆ A)).card)
          (((ADR11.roots G).filter (fun C => C ⊆ univ \ A)).card)) :
    pureRootSplitPayoff F A =
      rootSplitValue (((ADR11.roots F).filter (fun C => C ⊆ A)).card)
        (((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card) := by
  let a := ((ADR11.roots F).filter (fun C => C ⊆ A)).card
  let b := ((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card
  have hab : (ADR11.roots F).card = a + b := by
    obtain ⟨he, hd⟩ := Combinatorics.roots_color_partition F hF A hpure
    have hh := congrArg Finset.card he
    rw [card_union_of_disjoint hd] at hh
    exact hh
  have hpos := Combinatorics.colored_roots_positive F hF A hA hAc hcov hpure
  have hterm : ∀ G ∈ ADR11.merges F,
      pureRootSplitPayoff G A =
        (if ∀ C ∈ G \ F, C ⊆ A then rootSplitValue (a - 1) b else 0) +
        (if ∀ C ∈ G \ F, C ⊆ univ \ A then rootSplitValue a (b - 1) else 0) := by
    intro G hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
    simp only [new_clade_within_iff F A B C hB hC hBC,
      new_clade_within_iff F (univ \ A) B C hB hC hBC]
    by_cases hUA : B ∪ C ⊆ A
    · have hBA := subset_union_left.trans hUA
      have hCA := subset_union_right.trans hUA
      have hBn := not_subset_complement F hF A B hB hBA
      have hCn := not_subset_complement F hF A C hC hCA
      have hUn : ¬B ∪ C ⊆ univ \ A := fun h => hBn (subset_union_left.trans h)
      rw [ite_eq_left hUA, ite_eq_right hUn, add_zero]
      rw [hnext _ hG (pure_after_insert F A _ hpure (Or.inl hUA))]
      have ha := Combinatorics.card_roots_within_merge F hF A B C hB hC hBC hBA hCA
      have hb := Combinatorics.roots_within_merge_outside F hF (univ \ A) B C hB hC hBC hBn hCn
      rw [hb]
      congr 1
      change _ + 1 = a at ha
      omega
    · by_cases hUB : B ∪ C ⊆ univ \ A
      · have hBA := subset_union_left.trans hUB
        have hCA := subset_union_right.trans hUB
        have hBn := not_subset_original F hF A B hB hBA
        have hCn := not_subset_original F hF A C hC hCA
        rw [ite_eq_right hUA, ite_eq_left hUB, zero_add]
        rw [hnext _ hG (pure_after_insert F A _ hpure (Or.inr hUB))]
        have hb := Combinatorics.card_roots_within_merge F hF (univ \ A) B C hB hC hBC hBA hCA
        have ha := Combinatorics.roots_within_merge_outside F hF A B C hB hC hBC hBn hCn
        rw [ha]
        congr 1
        change _ + 1 = b at hb
        omega
      · rw [ite_eq_right hUA, ite_eq_right hUB, zero_add]
        unfold pureRootSplitPayoff
        exact mixed_split_history_payoff_zero _ (hF.isForest_merge hB hC) _ A
          (B ∪ C) (mem_insert_self _ _)
          (Combinatorics.merge_union_ne_univ_of_three_roots F hF B C hB hC hBC hk) hUA hUB
  have hrec : pureRootSplitPayoff F A =
      ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ *
        ((a.choose 2 : ℝ) * rootSplitValue (a - 1) b +
          (b.choose 2 : ℝ) * rootSplitValue a (b - 1)) := by
    unfold pureRootSplitPayoff
    rw [show (ADR11.roots F).card - 1 = ((ADR11.roots F).card - 2) + 1 by omega,
      Combinatorics.history_payoff_succ]
    have hs : ∀ G ∈ ADR11.merges F,
        Combinatorics.historyPayoff G ((ADR11.roots F).card - 2)
          (fun H => if ADR11.roots (H.erase univ) = {A, univ \ A} then 1 else 0) =
            pureRootSplitPayoff G A := by
      intro G hG
      unfold pureRootSplitPayoff
      congr 1
      have hh := (hF.of_mem_merges hG).2.1
      omega
    simp_rw [ADR11.jumpMatrix_apply_of_isForest (by omega : 1 < (ADR11.roots F).card)]
    rw [show (∑ G ∈ ADR11.merges F,
      (if G ∈ ADR11.merges F then ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ else 0) *
      Combinatorics.historyPayoff G ((ADR11.roots F).card - 2)
        (fun H => if ADR11.roots (H.erase univ) = {A, univ \ A} then 1 else 0)) =
      ∑ G ∈ ADR11.merges F, ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ *
      Combinatorics.historyPayoff G ((ADR11.roots F).card - 2)
        (fun H => if ADR11.roots (H.erase univ) = {A, univ \ A} then 1 else 0) from
      sum_congr rfl (fun G hG => by rw [ite_eq_left hG])]
    rw [← mul_sum]
    congr 1
    calc
      _ = ∑ G ∈ ADR11.merges F,
          ((if ∀ C ∈ G \ F, C ⊆ A then rootSplitValue (a - 1) b else 0) +
            (if ∀ C ∈ G \ F, C ⊆ univ \ A then rootSplitValue a (b - 1) else 0)) := by
        apply sum_congr rfl
        intro G hG
        rw [hs G hG, hterm G hG]
      _ = _ := by
        rw [sum_add_distrib, ← sum_filter, ← sum_filter]
        simp only [sum_const, nsmul_eq_mul, Combinatorics.card_merges_within F hF A,
          Combinatorics.card_merges_within F hF (univ \ A)]
        rfl
  rw [hrec, ← rootSplitValue_harmonic a b hpos.1 hpos.2 (by omega), hab]
  have hc : ((a + b).choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
end Rhone.Coalescent
