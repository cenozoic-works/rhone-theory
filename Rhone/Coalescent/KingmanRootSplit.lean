/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSplitSteps
/-!
# Root-split probabilities proved from chronological Kingman histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem pure_root_split_payoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A) :
    pureRootSplitPayoff F A =
      (2 : ℝ) / (((ADR11.roots F).card - 1 : ℕ) *
        ((ADR11.roots F).card.choose
          (((ADR11.roots F).filter (fun C => C ⊆ A)).card) : ℝ)) := by
  have main : ∀ k : ℕ, ∀ H : Finset (Finset L), (ADR11.roots H).card = k →
      ADR11.IsForest H → ADR11.lineages H = univ →
      (∀ C ∈ H, C ⊆ A ∨ C ⊆ univ \ A) →
      pureRootSplitPayoff H A =
        rootSplitValue (((ADR11.roots H).filter (fun C => C ⊆ A)).card)
          (((ADR11.roots H).filter (fun C => C ⊆ univ \ A)).card) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro H hk hH hcovH hpureH
      obtain ⟨ha, hb⟩ := Combinatorics.colored_roots_positive H hH A hA hAc hcovH hpureH
      obtain ⟨hpart, hd⟩ := Combinatorics.roots_color_partition H hH A hpureH
      have hab := congrArg Finset.card hpart
      rw [card_union_of_disjoint hd] at hab
      by_cases htwo : (ADR11.roots H).card = 2
      · rw [pure_root_split_payoff_two H hH A hA hAc hcovH hpureH htwo]
        have ha1 : ((ADR11.roots H).filter (fun C => C ⊆ A)).card = 1 := by omega
        have hb1 : ((ADR11.roots H).filter (fun C => C ⊆ univ \ A)).card = 1 := by omega
        rw [ha1, hb1]
        norm_num [rootSplitValue]
      · apply pure_root_split_history_step H hH A hA hAc hcovH hpureH (by omega)
        intro G hG hpureG
        obtain ⟨hGf, hGr, _, _, hGl⟩ := hH.of_mem_merges hG
        exact ih (ADR11.roots G).card (by omega) G rfl hGf (hGl.trans hcovH) hpureG
  have hm := main (ADR11.roots F).card F rfl hF hcov hpure
  obtain ⟨hpart, hd⟩ := Combinatorics.roots_color_partition F hF A hpure
  have hab := congrArg Finset.card hpart
  rw [card_union_of_disjoint hd] at hab
  simpa only [rootSplitValue, ← hab] using hm
noncomputable def rootSplitMass (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  ∑ h : Combinatorics.RankedLabelledHistory n,
    if ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A} then Combinatorics.historyMass (ADR11.singletonForest n) (n - 1) h else 0
theorem root_split_mass (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA0 : 0 < A.card) (hAn : A.card < n) :
    rootSplitMass n A = (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hAc : (univ \ A).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_fin]
    exact Nat.sub_pos_of_lt hAn
  have hpure : ∀ C ∈ ADR11.singletonForest n, C ⊆ A ∨ C ⊆ univ \ A := by
    intro C hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    by_cases hx : x ∈ A
    · exact Or.inl (singleton_subset_iff.mpr hx)
    · exact Or.inr (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ x, hx⟩))
  have hcount : ((ADR11.roots (ADR11.singletonForest n)).filter
      (fun C => C ⊆ A)).card = A.card := by
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
    rw [he, card_image_of_injective _ (by intro x y h; simpa using h)]
  have hm := pure_root_split_payoff (ADR11.singletonForest n)
    (ADR11.isForest_singletonForest n) A (card_pos.mp hA0) hAc
    (ADR11.absorb_lineages_singletonForest n) hpure
  rw [ADR11.card_roots_singletonForest, hcount] at hm
  rw [← hm]
  unfold rootSplitMass pureRootSplitPayoff Combinatorics.historyPayoff
  rw [ADR11.card_roots_singletonForest]
  apply sum_congr rfl
  intro h hh
  by_cases he : ADR11.roots
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
    {A, univ \ A}
  · simp only [he, ite_true, mul_one]
  · simp only [he, ite_false, mul_zero]
end Rhone.Coalescent
