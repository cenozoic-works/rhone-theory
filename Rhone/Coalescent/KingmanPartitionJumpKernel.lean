/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanPartition
public import Rhone.MarkovChain.Trajectory
public import Mathlib.Probability.UniformOn
/-! # The existing partition jump kernel as a uniform merger law -/
@[expose] public section
namespace Rhone.Coalescent
open Finset MeasureTheory ProbabilityTheory MarkovChain
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Source: kingman1982, Thm 1, eq. (2.2). -/
theorem partition_jump_prob {π : Finpartition (univ : Finset L)}
    (hk : 2 ≤ π.parts.card) (σ : Finpartition (univ : Finset L)) :
    (partitionChain L).jumpChain.P π σ =
      if σ ∈ merges π then ((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ else 0 := by
  classical
  have hr : (coalRate π.parts.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (coalRate_pos (by omega)))
  rw [RateChain.jumpChain_P, RateChain.jumpMatrix, partitionChain_rate,
    ite_eq_right hr, partitionChain_Q]
  by_cases he : π = σ
  · subst σ
    simp [self_notMem_merges]
  · by_cases hs : σ ∈ merges π
    · simp [he, partitionQ, Ne.symm he, coalRate_cast_eq_choose, hs]
    · simp [he, partitionQ, Ne.symm he, coalRate_cast_eq_choose, hs]

/-- Source: kingman1982, Thm 1, eq. (2.2). -/
theorem partition_jump_kernel_uniform {π : Finpartition (univ : Finset L)}
    (hk : 2 ≤ π.parts.card) :
    (partitionChain L).jumpChain.kernel π = uniformOn (merges π : Set _) := by
  classical
  apply Measure.ext_of_singleton
  intro σ
  rw [FinChain.kernel_apply_singleton, partition_jump_prob hk]
  rw [← Finset.coe_singleton σ, uniformOn_apply_finset, card_merges]
  by_cases hs : σ ∈ merges π
  · have hp : 0 < ((π.parts.card.choose 2 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hk)
    simp [hs, inter_singleton_of_mem, ENNReal.ofReal_inv_of_pos hp]
  · simp [hs, inter_singleton_of_notMem]

/-- Source: kingman1982, eq. (1.10). -/
theorem partition_jump_kernel_absorbing {π : Finpartition (univ : Finset L)}
    (hk : π.parts.card ≤ 1) :
    (partitionChain L).jumpChain.kernel π = Measure.dirac π := by
  classical
  have hr : (partitionChain L).rate π = 0 := by
    rw [partitionChain_rate, coalRate_eq_zero hk, Rat.cast_zero]
  apply Measure.ext_of_singleton
  intro σ
  rw [FinChain.kernel_apply_singleton]
  by_cases he : π = σ
  · subst σ
    simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr]
  · simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr, he]
end Rhone.Coalescent
