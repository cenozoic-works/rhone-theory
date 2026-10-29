/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanSubtreeMerges
public import Rhone.Coalescent.KingmanRootSampling
/-! # Split-supported terminal subtree payoffs -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def splitHistoryPayoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A : Finset L)
    (f g : Finset (Finset L) → ℝ) : ℝ :=
  Combinatorics.historyPayoff F ((ADR11.roots F).card - 1)
    (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then
      f (G.filter (fun C => C ⊆ A)) * g (G.filter (fun C => C ⊆ univ \ A)) else 0)
theorem mixed_subtree_history_payoff_zero
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ) (A C : Finset L)
    (hC : C ∈ F) (hCu : C ≠ univ) (hCA : ¬C ⊆ A) (hCB : ¬C ⊆ univ \ A)
    (f g : Finset (Finset L) → ℝ) :
    Combinatorics.historyPayoff F t
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then
        f (G.filter (fun D => D ⊆ A)) * g (G.filter (fun D => D ⊆ univ \ A)) else 0) = 0 := by
  unfold Combinatorics.historyPayoff
  apply sum_eq_zero
  intro h hh
  dsimp only
  rw [ite_eq_right (Combinatorics.root_split_excludes_mixed_history F hF t h A C hC hCu hCA hCB),
      mul_zero]
theorem split_history_payoff_two {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hk : (ADR11.roots F).card = 2) (f g : Finset (Finset L) → ℝ) :
    splitHistoryPayoff F A f g =
      f (F.filter (fun C => C ⊆ A)) * g (F.filter (fun C => C ⊆ univ \ A)) := by
  have hr := Combinatorics.two_color_roots_eq_pair F hF A hA hAc hcov hpure hk
  have hu : A ∪ (univ \ A) = univ := union_sdiff_of_subset (subset_univ A)
  have hAf : ¬univ ⊆ A := by
    intro ha
    obtain ⟨x, hx⟩ := hAc
    exact (mem_sdiff.mp hx).2 (ha (mem_univ x))
  have hAcf : ¬univ ⊆ univ \ A := by
    intro ha
    obtain ⟨x, hx⟩ := hA
    exact (mem_sdiff.mp (ha (mem_univ x))).2 hx
  have hend : ∀ h : Combinatorics.RankedForestHistory F 1, Combinatorics.historyEnd F 1 h = insert
      univ F := by
    intro h
    change h.1.1 = _
    obtain ⟨B, hB, C, hC, hBC, he⟩ := ADR11.mem_merges.mp h.1.2
    rw [hr, mem_insert, mem_singleton] at hB hC
    rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
    · exact (hBC rfl).elim
    · simpa only [hu] using he
    · simpa only [union_comm, hu] using he
    · exact (hBC rfl).elim
  have hfactor : splitHistoryPayoff F A f g = pureRootSplitPayoff F A *
      (f (F.filter (fun C => C ⊆ A)) * g (F.filter (fun C => C ⊆ univ \ A))) := by
    unfold splitHistoryPayoff pureRootSplitPayoff Combinatorics.historyPayoff
    rw [hk]
    change (∑ h : Combinatorics.RankedForestHistory F 1,
      Combinatorics.historyMass F 1 h *
        (if ADR11.roots ((Combinatorics.historyEnd F 1 h).erase univ) = {A, univ \ A} then
          f ((Combinatorics.historyEnd F 1 h).filter (fun C => C ⊆ A)) *
            g ((Combinatorics.historyEnd F 1 h).filter (fun C => C ⊆ univ \ A)) else 0)) = _
    rw [sum_mul]
    apply sum_congr rfl
    intro h hh
    rw [hend h]
    simp only [filter_insert, hAf, hAcf, ite_false]
    split_ifs <;> ring
  rw [hfactor, pure_root_split_payoff_two F hF A hA hAc hcov hpure hk, one_mul]
end Rhone.Coalescent
