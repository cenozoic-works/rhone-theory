/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanFlatLaw
public import Rhone.Coalescent.SmcPrimeOldTreeCoalExposure

/-! # Supported old pair densities equal the exponential of the all-pair exposure -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oldPairHistory_pair_data (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ)
    (τ : Fin (N - 1) → ℝ) (hs : KingmanHistorySupported N (oldPairHistory N w τ))
    (j : Fin (N - 1)) :
    let h := oldPairHistory N w τ
    1 < (h ⟨j.val, by omega⟩).1.2.2.1 ∧
      (w j).1 < (w j).2 ∧ (w j).2 < (h ⟨j.val, by omega⟩).1.2.2.1 ∧
      (h ⟨j.val, by omega⟩).1.1 < τ j ∧ (h ⟨j.val + 1, by omega⟩).1.1 = τ j := by
  let h := oldPairHistory N w τ
  have hc := (hs.1 (⟨j.val, by omega⟩ : Fin N)).2
  have hm : 2 ≤ (h ⟨j.val, by omega⟩).1.2.2.1 := by
    dsimp only [h] at hc ⊢
    rw [hc]
    have := j.isLt
    omega
  obtain ⟨ij, hij, hj, hev, _, ht⟩ := (ite_eq_left hm).mp (hs.2.2 j)
  have hmark : (h ⟨j.val + 1, by omega⟩).2.2 = .inr (.inl (w j)) := by
    simp only [h, oldPairHistory, argFlatRun, dite_eq_left j.isLt, argFlatActionStep]
  have htime : (h ⟨j.val + 1, by omega⟩).1.1 = τ j := by
    simp only [h, oldPairHistory, argFlatRun, dite_eq_left j.isLt, argFlatActionStep, atTime]
  have he : ij = w j := Sum.inl.inj (Sum.inr.inj (hev.symm.trans hmark))
  subst ij
  exact ⟨Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hm, hij, hj, htime ▸ ht, htime⟩

theorem oldPairDensity_eq_exposure (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ)
    (τ : Fin (N - 1) → ℝ) (hs : KingmanHistorySupported N (oldPairHistory N w τ)) :
    oldPairDensity N w τ =
      ENNReal.ofReal (Real.exp (-oldCoalExposure N (oldPairHistory N w τ))) := by
  classical
  let h := oldPairHistory N w τ
  have hweight (j : Fin (N - 1)) :
      argFlatActionWeight 0 (h ⟨j.val, by omega⟩) (.inl (w j)) (τ j) 0 =
        ENNReal.ofReal (Real.exp (-(totalRate false 0 (h ⟨j.val, by omega⟩).1 : ℝ) *
          ((h ⟨j.val + 1, by omega⟩).1.1 - (h ⟨j.val, by omega⟩).1.1))) := by
    obtain ⟨hm, hij, hj, ht, htime⟩ := oldPairHistory_pair_data N w τ hs j
    change 1 < (h ⟨j.val, by omega⟩).1.2.2.1 at hm
    change (w j).2 < (h ⟨j.val, by omega⟩).1.2.2.1 at hj
    change (h ⟨j.val, by omega⟩).1.1 < τ j at ht
    change (h ⟨j.val + 1, by omega⟩).1.1 = τ j at htime
    have hg : 1 < (h ⟨j.val, by omega⟩).1.2.2.1 ∧ (w j).1 < (w j).2 ∧
        (w j).2 < (h ⟨j.val, by omega⟩).1.2.2.1 ∧ (h ⟨j.val, by omega⟩).1.1 < τ j :=
      ⟨hm, hij, hj, ht⟩
    simp only [argFlatActionWeight, argFlatPairWeight, ite_eq_left hg, htime]
  unfold oldPairDensity argWordWeight
  rw [oldPairWord_fin_eq]
  have hw (j : Fin (N - 1)) : oldPairWord N w j.val = .inl (w j) := by
    simp only [oldPairWord, dite_eq_left j.isLt]
  simp only [hw]
  change (∏ j, argFlatActionWeight 0 (h ⟨j.val, by omega⟩) (.inl (w j)) (τ j) 0) = _
  rw [Finset.prod_congr rfl (fun j _ => hweight j),
    ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum]
  rw [oldCoalExposure_eq_rate_zero N h hs, ← Finset.sum_neg_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

end Rhone.Coalescent.SmcPrime
