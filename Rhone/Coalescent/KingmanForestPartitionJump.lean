/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import ADR11.Coalescent.Factorization
public import Rhone.Coalescent.KingmanForestPartitionMerges

/-!
# Forest roots and the Kingman partition jump chain

Uses `lean4-adr11` by The-Anh Vu-Le. -/

@[expose] public section

namespace Rhone.Coalescent.External.ADR11

open Finset _root_.ADR11

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem sum_jumpMatrix_roots_eq_partitionJump {F : Finset (Finset L)} (hF : IsForest F)
    (π σ : Finpartition (univ : Finset L)) (hπ : π.parts = roots F) :
    (∑ G ∈ univ.filter (fun G : Finset (Finset L) => roots G = σ.parts), jumpMatrix F G) =
    (partitionChain L).jumpChain.P π σ := by
  have he : roots F = σ.parts ↔ π = σ := by
    rw [← hπ]
    exact ⟨Finpartition.ext, congrArg Finpartition.parts⟩
  by_cases ht : (roots F).card ≤ 1
  · have hr : (partitionChain L).rate π = 0 := by
      rw [partitionChain_rate, hπ, coalRate_eq_zero ht]
      norm_num
    simp [jumpMatrix, ht, Rhone.MarkovChain.RateChain.jumpChain_P,
      Rhone.MarkovChain.RateChain.jumpMatrix, hr, he]
  · have hk : 2 ≤ (roots F).card := by omega
    have hr : (coalRate π.parts.card : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (coalRate_pos (by rw [hπ]; omega)))
    simp_rw [jumpMatrix_apply_of_isForest hk]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hf : (univ.filter (fun G : Finset (Finset L) => roots G = σ.parts)).filter
        (fun G => G ∈ _root_.ADR11.merges F) =
        (_root_.ADR11.merges F).filter (fun G => roots G = σ.parts) := by
      ext G
      simp [and_comm]
    rw [hf, card_merges_filter_roots hF hπ]
    rw [Rhone.MarkovChain.RateChain.jumpChain_P, Rhone.MarkovChain.RateChain.jumpMatrix,
      partitionChain_rate, ite_eq_right hr, partitionChain_Q]
    by_cases hsame : π = σ
    · subst σ
      simp [Rhone.Coalescent.self_notMem_merges]
    · simp only [hsame, ↓reduceIte, partitionQ, Ne.symm hsame, sub_zero]
      rw [← hπ, coalRate_cast_eq_choose]
      by_cases hσ : σ ∈ Rhone.Coalescent.merges π <;> simp [hσ, one_div]

end Rhone.Coalescent.External.ADR11
