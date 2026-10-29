/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanSubtreeStep
/-!
# Conditional terminal subtree payoff factorization for Kingman histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem split_history_payoff_factorization {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (f g : Finset (Finset L) → ℝ) :
    splitHistoryPayoff F A f g = pureRootSplitPayoff F A *
      Combinatorics.historyPayoff (F.filter (fun C => C ⊆ A))
        (((ADR11.roots F).filter (fun C => C ⊆ A)).card - 1) f *
      Combinatorics.historyPayoff (F.filter (fun C => C ⊆ univ \ A))
        (((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card - 1) g := by
  have main : ∀ k : ℕ, ∀ H : Finset (Finset L), (ADR11.roots H).card = k →
      ADR11.IsForest H → ADR11.lineages H = univ →
      (∀ C ∈ H, C ⊆ A ∨ C ⊆ univ \ A) →
      splitHistoryPayoff H A f g =
        rootSplitValue (((ADR11.roots H).filter (fun C => C ⊆ A)).card)
          (((ADR11.roots H).filter (fun C => C ⊆ univ \ A)).card) *
        Combinatorics.historyPayoff (H.filter (fun C => C ⊆ A))
          (((ADR11.roots H).filter (fun C => C ⊆ A)).card - 1) f *
        Combinatorics.historyPayoff (H.filter (fun C => C ⊆ univ \ A))
          (((ADR11.roots H).filter (fun C => C ⊆ univ \ A)).card - 1) g := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro H hk hH hcovH hpureH
      obtain ⟨ha, hb⟩ := Combinatorics.colored_roots_positive H hH A hA hAc hcovH hpureH
      obtain ⟨hpart, hd⟩ := Combinatorics.roots_color_partition H hH A hpureH
      have hab := congrArg Finset.card hpart
      rw [card_union_of_disjoint hd] at hab
      by_cases htwo : (ADR11.roots H).card = 2
      · rw [split_history_payoff_two H hH A hA hAc hcovH hpureH htwo f g]
        have ha1 : ((ADR11.roots H).filter (fun C => C ⊆ A)).card = 1 := by omega
        have hb1 : ((ADR11.roots H).filter (fun C => C ⊆ univ \ A)).card = 1 := by omega
        rw [ha1, hb1]
        have hf0 : Combinatorics.historyPayoff (H.filter (fun C => C ⊆ A)) 0 f =
            f (H.filter (fun C => C ⊆ A)) := by
          unfold Combinatorics.historyPayoff
          change (∑ h : PUnit, 1 * f (H.filter (fun C => C ⊆ A))) = _
          simp
        have hg0 : Combinatorics.historyPayoff (H.filter (fun C => C ⊆ univ \ A)) 0 g =
            g (H.filter (fun C => C ⊆ univ \ A)) := by
          unfold Combinatorics.historyPayoff
          change (∑ h : PUnit, 1 * g (H.filter (fun C => C ⊆ univ \ A))) = _
          simp
        have hv : rootSplitValue 1 1 = 1 := by norm_num [rootSplitValue]
        rw [hv, one_mul, hf0, hg0]
      · apply pure_subtree_history_step H hH A hA hAc hcovH hpureH (by omega) f g
        intro G hG hpureG
        obtain ⟨hGf, hGr, _, _, hGl⟩ := hH.of_mem_merges hG
        exact ih (ADR11.roots G).card (by omega) G rfl hGf (hGl.trans hcovH) hpureG
  have hm := main (ADR11.roots F).card F rfl hF hcov hpure
  obtain ⟨hpart, hd⟩ := Combinatorics.roots_color_partition F hF A hpure
  have hab := congrArg Finset.card hpart
  rw [card_union_of_disjoint hd] at hab
  have hp : pureRootSplitPayoff F A =
      rootSplitValue (((ADR11.roots F).filter (fun C => C ⊆ A)).card)
        (((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card) := by
    rw [pure_root_split_payoff F hF A hA hAc hcov hpure]
    unfold rootSplitValue
    rw [← hab]
  rw [hp]
  exact hm
end Rhone.Coalescent
