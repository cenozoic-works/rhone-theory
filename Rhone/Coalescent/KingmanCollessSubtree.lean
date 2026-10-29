/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanColless
public import Rhone.Coalescent.KingmanSingletonEmbedding
public import Rhone.Coalescent.KingmanHistoryEmbedding
public import Rhone.Coalescent.KingmanSubtreeFactorization
public import Rhone.Coalescent.KingmanRootSampling
/-!
# Colless payoffs in smaller labelled subtree history models

Source: cardona2013balance, §7; kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
theorem colless_subtree_payoff (n a : ℕ) (A : Finset (Fin n)) (e : Fin a ↪ Fin n)
    (he : (univ : Finset (Fin a)).map e = A) :
    Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ A)) (a - 1)
      (fun G => (treeColless G : ℝ)) =
    Combinatorics.historyPayoff (ADR11.singletonForest a) (a - 1)
        (fun G => (treeColless G : ℝ)) := by
  rw [← he, ← singletonForest_forestEmbed, historyPayoff_forestEmbed]
  simp_rw [treeColless_forestEmbed]
theorem colless_subtree_root_count (n a : ℕ) (A : Finset (Fin n)) (e : Fin a ↪ Fin n)
    (he : (univ : Finset (Fin a)).map e = A) :
    (((ADR11.roots (ADR11.singletonForest n)).filter (fun C => C ⊆ A)).card) = a := by
  rw [ADR11.roots_singletonForest, ← he, ← singletonForest_forestEmbed]
  unfold forestEmbed
  rw [card_image_of_injective _ (map_injective e),
    ← ADR11.roots_singletonForest, ADR11.card_roots_singletonForest]
/-- Source: cardona2013balance, §7. -/
theorem colless_split_subtree_payoff (n a b : ℕ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (hB : (univ \ A).Nonempty) (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (he : (univ : Finset (Fin a)).map e = A)
    (hf : (univ : Finset (Fin b)).map f = univ \ A) :
    splitHistoryPayoff (ADR11.singletonForest n) A (fun G => (treeColless G : ℝ))
      (fun _ => 1) = rootSplitMass n A *
        Combinatorics.historyPayoff (ADR11.singletonForest a) (a - 1)
            (fun G => (treeColless G : ℝ)) := by
  have hpure : ∀ C ∈ ADR11.singletonForest n, C ⊆ A ∨ C ⊆ univ \ A := by
    intro C hc
    obtain ⟨x, _, rfl⟩ := mem_image.mp hc
    by_cases hx : x ∈ A
    · exact Or.inl (singleton_subset_iff.mpr hx)
    · exact Or.inr (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ x, hx⟩))
  rw [split_history_payoff_factorization _ (ADR11.isForest_singletonForest n) A hA hB
    (ADR11.absorb_lineages_singletonForest n) hpure]
  rw [colless_subtree_root_count n a A e he,
    colless_subtree_root_count n b (univ \ A) f hf,
    colless_subtree_payoff n a A e he]
  have hbforest : ADR11.IsForest ((ADR11.singletonForest n).filter (fun C => C ⊆ univ \ A)) := by
    rw [← hf, ← singletonForest_forestEmbed]
    exact (isForest_forestEmbed_iff f _).mpr (ADR11.isForest_singletonForest b)
  have hbroot : (ADR11.roots ((ADR11.singletonForest n).filter
      (fun C => C ⊆ univ \ A))).card = b := by
    rw [← hf, ← singletonForest_forestEmbed, card_roots_forestEmbed,
      ADR11.card_roots_singletonForest]
  rw [history_payoff_one _ hbforest (b - 1) (by rw [hbroot]), mul_one]
  congr 1
  unfold pureRootSplitPayoff rootSplitMass Combinatorics.historyPayoff
  rw [ADR11.card_roots_singletonForest]
  apply sum_congr rfl
  intro h hh
  split_ifs <;> simp_all
end Rhone.Coalescent
