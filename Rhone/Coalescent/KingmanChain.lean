/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.JumpHold
public import Rhone.Coalescent.Kingman

/-! # Kingman's block-counting chain as a continuous-time chain -/

@[expose] public section

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain
open scoped ENNReal

theorem coalRate_nonneg (k : ℕ) : 0 ≤ coalRate k := by
  rcases k with _ | k
  · simp [coalRate]
  · unfold coalRate
    push_cast
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    nlinarith

theorem coalRate_eq_zero {k : ℕ} (hk : k ≤ 1) : coalRate k = 0 := by
  interval_cases k <;> simp [coalRate]

noncomputable def blockQ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun k j =>
  (coalRate k : ℝ) * ((if (j : ℕ) + 1 = k then 1 else 0) - (if j = k then 1 else 0))

theorem sum_blockQ_mul (n : ℕ) (k : Fin (n + 1)) (hk : 1 ≤ (k : ℕ)) (u : Fin (n + 1) → ℝ) :
    ∑ j, blockQ n k j * u j =
      (coalRate k : ℝ) * (u ⟨(k : ℕ) - 1, by omega⟩ - u k) := by
  have hterm : ∀ j : Fin (n + 1), blockQ n k j * u j = (coalRate k : ℝ) *
      ((if (j : ℕ) + 1 = k then u j else 0) - (if j = k then u j else 0)) := by
    intro j
    unfold blockQ
    split_ifs <;> ring
  simp only [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq' univ k u]
  congr 2
  · rw [Finset.sum_eq_single (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1))]
    · rw [ite_eq_left (by simp only; omega)]
    · intro j _ hj
      refine ite_eq_right fun h => hj (Fin.ext ?_)
      simp only
      omega
    · intro h
      exact absurd (mem_univ _) h
  · simp

noncomputable def blockChain (n : ℕ) : RateChain (Fin (n + 1)) where
  Q := blockQ n
  off_diag_nonneg k j hkj := by
    have hc : (0 : ℝ) ≤ (coalRate k : ℝ) := by exact_mod_cast coalRate_nonneg k
    have hjk : j ≠ k := fun h => hkj h.symm
    unfold blockQ
    rw [ite_eq_right (c := j = k) hjk, sub_zero]
    exact mul_nonneg hc (by split_ifs <;> norm_num)
  row_sum k := by
    by_cases hk : 1 ≤ (k : ℕ)
    · have h := sum_blockQ_mul n k hk (fun _ => 1)
      simpa using h
    · have h0 : coalRate (k : ℕ) = 0 := coalRate_eq_zero (by omega)
      simp [blockQ, h0]

theorem blockChain_Q (n : ℕ) : (blockChain n).Q = blockQ n := rfl

theorem blockChain_rate (n : ℕ) (k : Fin (n + 1)) : (blockChain n).rate k = (coalRate k : ℝ) := by
  simp [RateChain.rate, blockChain_Q, blockQ]

def coalesced (n : ℕ) : Finset (Fin (n + 1)) := univ.filter fun k => (k : ℕ) ≤ 1

theorem mem_coalesced {n : ℕ} {k : Fin (n + 1)} : k ∈ coalesced n ↔ (k : ℕ) ≤ 1 := by
  simp [coalesced]

theorem blockChain_isAbsorbingSet (n : ℕ) :
    (blockChain n).jumpChain.IsAbsorbingSet (coalesced n) :=
  RateChain.jumpChain_isAbsorbingSet fun a ha => by
    rw [blockChain_rate, coalRate_eq_zero (mem_coalesced.1 ha), Rat.cast_zero]

theorem blockChain_rate_pos {n : ℕ} {k : Fin (n + 1)} (hk : k ∉ coalesced n) :
    0 < (blockChain n).rate k := by
  rw [mem_coalesced, not_le] at hk
  rw [blockChain_rate]
  exact_mod_cast coalRate_pos hk

theorem blockChain_reaches (n : ℕ) : (blockChain n).jumpChain.Reaches (coalesced n) := by
  refine FinChain.reaches_of_rank _ _ (fun k => (k : ℕ)) fun k hk => ?_
  have hk2 : 2 ≤ (k : ℕ) := by
    rw [mem_coalesced, not_le] at hk
    exact hk
  have hpos := blockChain_rate_pos hk
  have hne : k ≠ (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)) := fun h => by
    have := congrArg Fin.val h
    simp only at this
    omega
  refine ⟨⟨(k : ℕ) - 1, by omega⟩, ?_, by simp only; omega⟩
  rw [RateChain.jumpChain_P_of_ne hpos.ne' hne]
  refine div_pos ?_ hpos
  rw [blockChain_Q, blockQ, ite_eq_left (by simp only; omega), ite_eq_right hne.symm, sub_zero,
    mul_one, ← blockChain_rate]
  exact hpos

theorem blockChain_expectedCost (n : ℕ) (g : ℕ → ℝ) (k : Fin (n + 1)) :
    (blockChain n).expectedCost (coalesced n) (fun j => g j) k =
      ∑ j ∈ Icc 2 (k : ℕ), g j * (holdingTime j : ℝ) := by
  have key : ∀ m : ℕ, 2 ≤ m → ∑ j ∈ Icc 2 m, g j * (holdingTime j : ℝ) =
      ∑ j ∈ Icc 2 (m - 1), g j * (holdingTime j : ℝ) + g m * (holdingTime m : ℝ) := by
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp
  refine (congrFun (RateChain.eq_expectedCost_of_generator (blockChain_isAbsorbingSet n)
    (blockChain_reaches n) (fun x hx => (blockChain_rate_pos hx).ne')
    (u := fun x : Fin (n + 1) => ∑ j ∈ Icc 2 (x : ℕ), g j * (holdingTime j : ℝ))
    (fun a ha => ?_) fun x hx => ?_) k).symm
  · rw [Finset.Icc_eq_empty (by have := mem_coalesced.1 ha; omega), Finset.sum_empty]
  · have hx2 : 2 ≤ (x : ℕ) := by
      rw [mem_coalesced, not_le] at hx
      exact hx
    have hc : (coalRate (x : ℕ) : ℝ) * (holdingTime (x : ℕ) : ℝ) = 1 := by
      have hq : coalRate (x : ℕ) * holdingTime (x : ℕ) = 1 := by
        rw [holdingTime, mul_one_div, div_self (coalRate_pos hx2).ne']
      exact_mod_cast hq
    rw [blockChain_Q, sum_blockQ_mul n x (by omega)]
    simp only
    rw [key (x : ℕ) hx2]
    linear_combination (-(g (x : ℕ))) * hc

variable (n : ℕ)

noncomputable def tmrca (p : (ℕ → Fin (n + 1)) × (ℕ → ℝ)) : ℝ≥0∞ :=
  (blockChain n).timeBefore (coalesced n) p

noncomputable def treeLength (p : (ℕ → Fin (n + 1)) × (ℕ → ℝ)) : ℝ≥0∞ :=
  (blockChain n).costBefore (coalesced n) (fun k => ((k : ℕ) : ℝ)) p

theorem lintegral_tmrca :
    ∫⁻ p, tmrca n p ∂(blockChain n).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal (expTMRCA n : ℝ) := by
  unfold tmrca
  rw [RateChain.lintegral_timeBefore (blockChain_isAbsorbingSet n) (blockChain_reaches n),
    RateChain.expectedTime, blockChain_expectedCost n (fun _ => 1)]
  simp [expTMRCA]

theorem lintegral_treeLength :
    ∫⁻ p, treeLength n p ∂(blockChain n).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal (expLength n : ℝ) := by
  unfold treeLength
  rw [RateChain.lintegral_costBefore (blockChain_isAbsorbingSet n) (blockChain_reaches n)
    (fun k => Nat.cast_nonneg _), blockChain_expectedCost n (fun j => (j : ℝ))]
  simp [expLength]

end Rhone.Coalescent
