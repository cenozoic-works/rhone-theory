/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanColoredForest
public import Rhone.Combinatorics.KingmanHistoryPayoff
/-! # Root-split history payoff and its two-root base case -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def pureRootSplitPayoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A : Finset L) : ℝ :=
  Combinatorics.historyPayoff F ((ADR11.roots F).card - 1)
    (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then 1 else 0)
private theorem history_payoff_zero {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (f : Finset (Finset L) → ℝ) : Combinatorics.historyPayoff F 0 f = f F :=
        by
  unfold Combinatorics.historyPayoff
  change (∑ h : PUnit, 1 * f F) = f F
  simp

theorem pure_root_split_payoff_two
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hk : (ADR11.roots F).card = 2) : pureRootSplitPayoff F A = 1 := by
  have hr := Combinatorics.two_color_roots_eq_pair F hF A hA hAc hcov hpure hk
  have hne : A ≠ univ \ A := by
    intro he
    obtain ⟨x, hx⟩ := hA
    have hx' := hx
    rw [he] at hx'
    exact (mem_sdiff.mp hx').2 hx
  have hfullnot : univ ∉ F := by
    intro hf
    rcases hpure univ hf with ha | hb
    · obtain ⟨x, hx⟩ := hAc
      exact (mem_sdiff.mp hx).2 (ha (mem_univ x))
    · obtain ⟨x, hx⟩ := hA
      exact (mem_sdiff.mp (hb (mem_univ x))).2 hx
  have hu : A ∪ (univ \ A) = univ := by
    exact union_sdiff_of_subset (subset_univ A)
  have hm : ADR11.merges F = {insert univ F} := by
    ext G
    rw [ADR11.mem_merges, mem_singleton]
    constructor
    · rintro ⟨B, hB, C, hC, hBC, rfl⟩
      rw [hr, mem_insert, mem_singleton] at hB hC
      rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
      · exact (hBC rfl).elim
      · rw [hu]
      · rw [union_comm, hu]
      · exact (hBC rfl).elim
    · intro he
      refine ⟨A, ?_, univ \ A, ?_, hne, ?_⟩
      · rw [hr]; exact mem_insert_self _ _
      · rw [hr]; exact mem_insert_of_mem (mem_singleton_self _)
      · simpa only [hu] using he
  unfold pureRootSplitPayoff
  rw [hk]
  change Combinatorics.historyPayoff F 1 _ = 1
  rw [Combinatorics.history_payoff_succ F 0, hm, sum_singleton, history_payoff_zero]
  rw [ADR11.jumpMatrix_apply_of_isForest (by omega), hm]
  simp only [mem_singleton, ite_true, hk]
  norm_num [erase_eq_of_notMem hfullnot, hr]
end Rhone.Coalescent
