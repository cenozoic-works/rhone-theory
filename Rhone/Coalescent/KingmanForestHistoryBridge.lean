/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanForestPartitionJump
public import Rhone.Combinatorics.KingmanHistoryPayoff
/-! # Forest-history payoffs and partition-step expectations -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open External.ADR11 Combinatorics.External.ADR11
variable {L : Type*} [Fintype L] [DecidableEq L]

private theorem partition_jump_uniform {π : Finpartition (univ : Finset L)}
    (hk : 2 ≤ π.parts.card) (σ : Finpartition (univ : Finset L)) :
    (partitionChain L).jumpChain.P π σ =
      if σ ∈ merges π then ((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ else 0 := by
  have hr : (coalRate π.parts.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (coalRate_pos (by omega)))
  rw [Rhone.MarkovChain.RateChain.jumpChain_P, Rhone.MarkovChain.RateChain.jumpMatrix,
    partitionChain_rate, ite_eq_right hr, partitionChain_Q]
  by_cases he : π = σ
  · subst σ
    simp [self_notMem_merges]
  · by_cases hs : σ ∈ merges π
    · simp [he, partitionQ, Ne.symm he, coalRate_cast_eq_choose, hs]
    · simp [he, partitionQ, Ne.symm he, coalRate_cast_eq_choose, hs]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
private theorem sum_merges_transfer {F : Finset (Finset L)} (hF : ADR11.IsForest F)
    {π : Finpartition (univ : Finset L)} (hπ : π.parts = ADR11.roots F)
    (hk : 2 ≤ (ADR11.roots F).card) (u : Finset (Finset L) → ℝ)
    (v : Finpartition (univ : Finset L) → ℝ)
    (hu : ∀ G ∈ ADR11.merges F, ∀ τ : Finpartition (univ : Finset L),
      ADR11.roots G = τ.parts → u G = v τ) :
    (∑ G ∈ ADR11.merges F, ADR11.jumpMatrix F G * u G) =
      ∑ τ : Finpartition (univ : Finset L), (partitionChain L).jumpChain.P π τ * v τ := by
  classical
  let obs (G : Finset (Finset L)) (hG : G ∈ ADR11.merges F) :=
    (roots_eq_parts_of_mem_merges hF hπ hG).choose
  have ho G hG : obs G hG ∈ merges π ∧ ADR11.roots G = (obs G hG).parts :=
    (roots_eq_parts_of_mem_merges hF hπ hG).choose_spec
  simp_rw [partition_jump_uniform (π := π) (by simpa only [hπ] using hk), ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter]
  refine sum_bij obs (fun G hG => (ho G hG).1) ?_ ?_ ?_
  · intro G hG H hH heq
    apply roots_injective_on_merges hF hπ hG hH
    exact (ho G hG).2.trans ((congrArg Finpartition.parts heq).trans (ho H hH).2.symm)
  · intro τ hτ
    obtain ⟨G, hG, hr⟩ := exists_merge_roots_eq_of_mem_merges hF hπ hτ
    refine ⟨G, hG, Finpartition.ext ?_⟩
    exact (ho G hG).2.symm.trans hr
  · intro G hG
    rw [hu G hG (obs G hG) (ho G hG).2, ADR11.jumpMatrix_apply_of_isForest hk,
      ite_eq_left hG, hπ]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem historyPayoff_roots_eq_partition_stepN {F : Finset (Finset L)}
    (hF : ADR11.IsForest F) (π : Finpartition (univ : Finset L))
    (hπ : π.parts = ADR11.roots F) (t : ℕ) (ht : t ≤ (ADR11.roots F).card - 1)
    (f : Finset (Finset L) → ℝ) :
    Combinatorics.historyPayoff F t (fun G => f (ADR11.roots G)) =
      ∑ σ : Finpartition (univ : Finset L),
        (partitionChain L).jumpChain.stepN t π σ * f σ.parts := by
  induction t generalizing F π with
  | zero =>
    change (∑ _ : PUnit, 1 * f (ADR11.roots F)) = _
    simp [Rhone.MarkovChain.FinChain.stepN_zero, Matrix.one_apply, hπ]
  | succ t ih =>
    have hk : 2 ≤ (ADR11.roots F).card := by omega
    change Combinatorics.historyPayoff F (t + 1) _ =
      (partitionChain L).jumpChain.expectN (t + 1) (fun σ => f σ.parts) π
    rw [Combinatorics.history_payoff_succ, Rhone.MarkovChain.FinChain.expectN_succ,
      Rhone.MarkovChain.FinChain.expect_apply]
    apply sum_merges_transfer hF hπ hk
    intro G hG τ hr
    obtain ⟨hforest, hcard, -⟩ := hF.of_mem_merges hG
    exact ih hforest τ hr.symm (by omega)
end Rhone.Coalescent
