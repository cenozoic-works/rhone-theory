/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanSubtreeMergerPayoff
/-! # The first-merger induction step for restricted endpoint subtree payoffs -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem pure_subtree_history_step {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hk : 3 ≤ (ADR11.roots F).card) (f g : Finset (Finset L) → ℝ)
    (hnext : ∀ G ∈ ADR11.merges F,
      (∀ C ∈ G, C ⊆ A ∨ C ⊆ univ \ A) →
      splitHistoryPayoff G A f g =
        rootSplitValue (((ADR11.roots G).filter (fun C => C ⊆ A)).card)
          (((ADR11.roots G).filter (fun C => C ⊆ univ \ A)).card) *
        Combinatorics.historyPayoff (G.filter (fun C => C ⊆ A))
          (((ADR11.roots G).filter (fun C => C ⊆ A)).card - 1) f *
        Combinatorics.historyPayoff (G.filter (fun C => C ⊆ univ \ A))
          (((ADR11.roots G).filter (fun C => C ⊆ univ \ A)).card - 1) g) :
    splitHistoryPayoff F A f g =
      rootSplitValue (((ADR11.roots F).filter (fun C => C ⊆ A)).card)
        (((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card) *
      Combinatorics.historyPayoff (F.filter (fun C => C ⊆ A))
        (((ADR11.roots F).filter (fun C => C ⊆ A)).card - 1) f *
      Combinatorics.historyPayoff (F.filter (fun C => C ⊆ univ \ A))
        (((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card - 1) g := by
  classical
  let a := ((ADR11.roots F).filter (fun C => C ⊆ A)).card
  let b := ((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card
  let cA := Combinatorics.historyPayoff (F.filter (fun C => C ⊆ A)) (a - 1) f
  let cB := Combinatorics.historyPayoff (F.filter (fun C => C ⊆ univ \ A)) (b - 1) g
  change splitHistoryPayoff F A f g = rootSplitValue a b * cA * cB
  have hab : (ADR11.roots F).card = a + b := by
    obtain ⟨he, hd⟩ := Combinatorics.roots_color_partition F hF A hpure
    have hh := congrArg Finset.card he
    rw [card_union_of_disjoint hd] at hh
    exact hh
  have hpos := Combinatorics.colored_roots_positive F hF A hA hAc hcov hpure
  have hterm : ∀ G ∈ ADR11.merges F,
      splitHistoryPayoff G A f g =
        (if ∀ C ∈ G \ F, C ⊆ A then rootSplitValue (a - 1) b *
          Combinatorics.historyPayoff (G.filter (fun C => C ⊆ A)) (a - 2) f * cB else 0) +
        (if ∀ C ∈ G \ F, C ⊆ univ \ A then rootSplitValue a (b - 1) * cA *
          Combinatorics.historyPayoff (G.filter (fun C => C ⊆ univ \ A)) (b - 2) g else 0) := by
    intro G hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
    have hU := ADR11.union_not_mem_of_mem_roots hB hC hBC
    have hequiv : ∀ X : Finset L,
        (∀ D ∈ insert (B ∪ C) F \ F, D ⊆ X) ↔ B ∪ C ⊆ X := by
      intro X
      constructor
      · intro h
        exact h _ (mem_sdiff.mpr ⟨mem_insert_self _ _, hU⟩)
      · intro h D hD
        obtain ⟨hD, hn⟩ := mem_sdiff.mp hD
        rcases mem_insert.mp hD with rfl | hD
        · exact h
        · exact (hn hD).elim
    simp only [hequiv]
    have hp : (B ∪ C ⊆ A ∨ B ∪ C ⊆ univ \ A) →
        ∀ D ∈ insert (B ∪ C) F, D ⊆ A ∨ D ⊆ univ \ A := by
      intro h D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact h
      · exact hpure D hD
    by_cases hUA : B ∪ C ⊆ A
    · have hBA := subset_union_left.trans hUA
      have hCA := subset_union_right.trans hUA
      have hBn : ¬B ⊆ univ \ A := by
        intro h
        obtain ⟨x, hx⟩ := hF.1 B (ADR11.roots_subset F hB)
        exact (mem_sdiff.mp (h hx)).2 (hBA hx)
      have hCn : ¬C ⊆ univ \ A := by
        intro h
        obtain ⟨x, hx⟩ := hF.1 C (ADR11.roots_subset F hC)
        exact (mem_sdiff.mp (h hx)).2 (hCA hx)
      have hUn : ¬B ∪ C ⊆ univ \ A := fun h => hBn (subset_union_left.trans h)
      have ha := Combinatorics.card_roots_within_merge F hF A B C hB hC hBC hBA hCA
      have hae : ((ADR11.roots (insert (B ∪ C) F)).filter (fun D => D ⊆ A)).card =
          a - 1 := by change _ + 1 = a at ha; omega
      have hb := Combinatorics.roots_within_merge_outside F hF (univ \ A) B C hB hC hBC hBn hCn
      have hfb : (insert (B ∪ C) F).filter (fun D => D ⊆ univ \ A) =
          F.filter (fun D => D ⊆ univ \ A) := by rw [filter_insert, ite_eq_right hUn]
      rw [ite_eq_left hUA, ite_eq_right hUn, add_zero,
        hnext _ hG (hp (Or.inl hUA)), hae, hb, hfb]
      change rootSplitValue (a - 1) b * _ * cB = _
      rw [show a - 1 - 1 = a - 2 by omega]
    · by_cases hUB : B ∪ C ⊆ univ \ A
      · have hBA := subset_union_left.trans hUB
        have hCA := subset_union_right.trans hUB
        have hBn : ¬B ⊆ A := by
          intro h
          obtain ⟨x, hx⟩ := hF.1 B (ADR11.roots_subset F hB)
          exact (mem_sdiff.mp (hBA hx)).2 (h hx)
        have hCn : ¬C ⊆ A := by
          intro h
          obtain ⟨x, hx⟩ := hF.1 C (ADR11.roots_subset F hC)
          exact (mem_sdiff.mp (hCA hx)).2 (h hx)
        have hb := Combinatorics.card_roots_within_merge F hF (univ \ A) B C hB hC hBC hBA hCA
        have hbe : ((ADR11.roots (insert (B ∪ C) F)).filter
            (fun D => D ⊆ univ \ A)).card = b - 1 := by
          change _ + 1 = b at hb
          omega
        have ha := Combinatorics.roots_within_merge_outside F hF A B C hB hC hBC hBn hCn
        have hfa : (insert (B ∪ C) F).filter (fun D => D ⊆ A) =
            F.filter (fun D => D ⊆ A) := by rw [filter_insert, ite_eq_right hUA]
        rw [ite_eq_right hUA, ite_eq_left hUB, zero_add,
          hnext _ hG (hp (Or.inr hUB)), ha, hbe, hfa]
        change rootSplitValue a (b - 1) * cA * _ = _
        rw [show b - 1 - 1 = b - 2 by omega]
      · rw [ite_eq_right hUA, ite_eq_right hUB, zero_add]
        unfold splitHistoryPayoff
        exact mixed_subtree_history_payoff_zero _ (hF.isForest_merge hB hC) _ A
          (B ∪ C) (mem_insert_self _ _)
          (Combinatorics.merge_union_ne_univ_of_three_roots F hF B C hB hC hBC hk) hUA hUB f g
  have hc : univ \ (univ \ A) = A := by ext x; simp
  have hpcomp : ∀ C ∈ F, C ⊆ univ \ A ∨ C ⊆ univ \ (univ \ A) := by
    intro C hC
    rw [hc]
    rcases hpure C hC with ha | hb
    · exact Or.inr ha
    · exact Or.inl hb
  have hsumA := sum_merges_within_history_payoff F hF A hpure f
  have hsumB := sum_merges_within_history_payoff F hF (univ \ A) hpcomp g
  change _ = (a.choose 2 : ℝ) * cA at hsumA
  change _ = (b.choose 2 : ℝ) * cB at hsumB
  have hrec : splitHistoryPayoff F A f g =
      ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ *
        (((a.choose 2 : ℝ) * rootSplitValue (a - 1) b +
          (b.choose 2 : ℝ) * rootSplitValue a (b - 1)) * cA * cB) := by
    unfold splitHistoryPayoff
    rw [show (ADR11.roots F).card - 1 = ((ADR11.roots F).card - 2) + 1 by omega,
      Combinatorics.history_payoff_succ]
    have hs : ∀ G ∈ ADR11.merges F,
        ADR11.jumpMatrix F G * Combinatorics.historyPayoff G ((ADR11.roots F).card - 2)
          (fun H => if ADR11.roots (H.erase univ) = {A, univ \ A} then
            f (H.filter (fun C => C ⊆ A)) * g (H.filter (fun C => C ⊆ univ \ A)) else 0) =
        ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ * splitHistoryPayoff G A f g := by
      intro G hG
      rw [ADR11.jumpMatrix_apply_of_isForest (by omega), ite_eq_left hG]
      congr 1
      unfold splitHistoryPayoff
      congr 1
      have hh := (hF.of_mem_merges hG).2.1
      omega
    rw [sum_congr rfl hs, ← mul_sum]
    congr 1
    calc
      _ = ∑ G ∈ ADR11.merges F,
          ((if ∀ C ∈ G \ F, C ⊆ A then rootSplitValue (a - 1) b *
            Combinatorics.historyPayoff (G.filter (fun C => C ⊆ A)) (a - 2) f * cB else 0) +
          (if ∀ C ∈ G \ F, C ⊆ univ \ A then rootSplitValue a (b - 1) * cA *
            Combinatorics.historyPayoff (G.filter (fun C => C ⊆ univ \ A)) (b - 2) g else 0)) := by
        exact sum_congr rfl (fun G hG => hterm G hG)
      _ = _ := by
        rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← sum_mul, ← mul_sum, ← mul_sum,
          hsumA, hsumB]
        ring
  rw [hrec, ← rootSplitValue_harmonic a b hpos.1 hpos.2 (by omega), hab]
  have hchoose : ((a + b).choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  simp only [← mul_assoc]
  rw [inv_mul_cancel₀ hchoose, one_mul]
end Rhone.Coalescent
