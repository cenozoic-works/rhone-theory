/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import ADR11.Coalescent.Factorization
public import Rhone.Statistics.External.ADR11

/-!
# Forest roots and the Kingman block jump chain

Uses `lean4-adr11` by The-Anh Vu-Le. -/

@[expose] public section

namespace Rhone.Statistics.External.ADR11

open Finset _root_.ADR11

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem jumpMatrix_eq_identity_add_generator {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ (roots F).card) (G : Finset (Finset L)) :
    jumpMatrix F G = (if G = F then 1 else 0) +
      kingmanGenerator F G / (Coalescent.coalRate (roots F).card : ℝ) := by
  have hr : (Coalescent.coalRate (roots F).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Coalescent.coalRate_pos (by omega)))
  rw [jumpMatrix_apply_of_isForest hk, kingmanGenerator_apply_of_isForest]
  rw [Coalescent.coalRate_eq_choose] at hr ⊢
  push_cast at hr ⊢
  by_cases h : G = F
  · subst G
    simp [hF.self_not_mem_merges, hr]
  · by_cases hm : G ∈ _root_.ADR11.merges F <;> simp [h, hm, one_div]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem sum_jumpMatrix_card_roots_eq_blockJump {n : ℕ} {F : Finset (Finset L)}
    (hF : IsForest F) (hk : (roots F).card < n + 1) (j : Fin (n + 1)) :
    (∑ G ∈ univ.filter (fun G : Finset (Finset L) => (roots G).card = (j : ℕ)),
      jumpMatrix F G) =
    (Coalescent.blockChain n).jumpChain.P ⟨(roots F).card, hk⟩ j := by
  have he : (⟨(roots F).card, hk⟩ : Fin (n + 1)) = j ↔ (roots F).card = (j : ℕ) :=
    Fin.ext_iff
  by_cases ht : (roots F).card ≤ 1
  · have hr : (Coalescent.blockChain n).rate ⟨(roots F).card, hk⟩ = 0 := by
      rw [Coalescent.blockChain_rate, Coalescent.coalRate_eq_zero ht]
      norm_num
    simp [jumpMatrix, ht, Rhone.MarkovChain.RateChain.jumpChain_P,
      Rhone.MarkovChain.RateChain.jumpMatrix, hr, he]
  · have hpos : 2 ≤ (roots F).card := by omega
    have hr : (Coalescent.coalRate (roots F).card : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Coalescent.coalRate_pos (by omega)))
    simp_rw [jumpMatrix_eq_identity_add_generator hF hpos]
    rw [sum_add_distrib, sum_ite_eq', ← sum_div,
      sum_kingmanGenerator_card_roots_eq_blockQ hF hk j]
    simp only [mem_filter, mem_univ, true_and]
    rw [Rhone.MarkovChain.RateChain.jumpChain_P, Rhone.MarkovChain.RateChain.jumpMatrix,
      Coalescent.blockChain_rate, ite_eq_right hr, Coalescent.blockChain_Q]
    by_cases hj : (roots F).card = (j : ℕ)
    · have hfin := he.mpr hj
      rw [ite_eq_left hj, ite_eq_left hfin]
      have hq : Coalescent.blockQ n ⟨(roots F).card, hk⟩ j =
          -(Coalescent.coalRate (roots F).card : ℝ) := by
        subst j
        simp [Coalescent.blockQ]
      rw [hq]
      simp [hr]
    · rw [ite_eq_right hj, ite_eq_right (fun h => hj (he.mp h))]
      simp

end Rhone.Statistics.External.ADR11
