/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisherAllocation

/-!
# Coordinate means of the multinomial Wright–Fisher chain

Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset

/-- Source: ewens2004, sec. 3.5. -/
private theorem allocation_marginal (N K : ℕ) (a : AlleleCounts N K)
    (t : Fin N) (l : Fin K) :
    (∑ ω : Fin N → Fin K,
      if ω t = l then wfMultialleleAllocationWeight N K a ω else 0) =
      (a.val l : ℝ) / N := by
  classical
  let p : Fin K → ℝ := fun c => (a.val c : ℝ) / N
  let g : Fin N → Fin K → ℝ := fun i c =>
    if i = t then (if c = l then p c else 0) else p c
  have hp : (∑ c : Fin K, p c) = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, a.sum_real, div_self (Nat.cast_ne_zero.mpr (Fin.pos t).ne')]
  have hprod (ω : Fin N → Fin K) :
      (∏ i : Fin N, g i (ω i)) =
        if ω t = l then wfMultialleleAllocationWeight N K a ω else 0 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g i (ω i)) (mem_univ t)]
    have her : (∏ i ∈ Finset.univ.erase t, g i (ω i)) =
        ∏ i ∈ Finset.univ.erase t, p (ω i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [g, ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [her]
    by_cases hω : ω t = l
    · simpa [g, hω, p, wfMultialleleAllocationWeight] using
        Finset.mul_prod_erase Finset.univ (fun i => p (ω i)) (mem_univ t)
    · simp [g, hω]
  have hg (i : Fin N) : (∑ c : Fin K, g i c) = if i = t then p l else 1 := by
    by_cases hi : i = t
    · subst i
      simp [g]
    · simp [g, hi, hp]
  calc
    _ = ∑ ω : Fin N → Fin K, ∏ i : Fin N, g i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (hprod ω).symm
    _ = ∏ i : Fin N, ∑ c : Fin K, g i c := (Fintype.prod_sum g).symm
    _ = p l := by simp_rw [hg]; simp
    _ = _ := rfl

/-- Source: ewens2004, sec. 3.5. -/
private theorem allele_le {N K : ℕ} (a : AlleleCounts N K) (l : Fin K) : a.val l ≤ N := by
  have h : a.val l ≤ ∑ c : Fin K, a.val c :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ l)
  exact h.trans_eq a.sum

/-- Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfMultiallele_expect_count (N K : ℕ) (a : AlleleCounts N K) (l : Fin K) :
    ∑ b : AlleleCounts N K, wfMultiallele N K a b * (b.val l : ℝ) = a.val l := by
  have hcount (ω : Fin N → Fin K) :
      ((wfAlleleAllocationCounts N K ω).val l : ℝ) =
        ∑ t : Fin N, if ω t = l then (1 : ℝ) else 0 := by
    have hn : (wfAlleleAllocationCounts N K ω).val l =
        ∑ t : Fin N, if ω t = l then 1 else 0 := by
      rw [wfAlleleAllocationCounts_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact_mod_cast hn
  calc
    _ = ∑ ω : Fin N → Fin K,
        wfMultialleleAllocationWeight N K a ω *
          ((wfAlleleAllocationCounts N K ω).val l : ℝ) :=
      WrightFisherAllocationSupport.expect N K a _
    _ = ∑ t : Fin N, ∑ ω : Fin N → Fin K,
        if ω t = l then wfMultialleleAllocationWeight N K a ω else 0 := by
      simp_rw [hcount, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
    _ = ∑ _t : Fin N, (a.val l : ℝ) / N := by
      apply Finset.sum_congr rfl
      intro t _
      exact allocation_marginal N K a t l
    _ = (N : ℝ) * ((a.val l : ℝ) / N) := by simp
    _ = a.val l := by
      by_cases hN : N = 0
      · have ha : a.val l = 0 := Nat.eq_zero_of_le_zero (hN ▸ allele_le a l)
        simp [hN, ha]
      · field_simp

/-- Source: ewens2004, sec. 3.5. -/
theorem wfMultialleleChain_expect_count (N K : ℕ) (a : AlleleCounts N K)
    (l : Fin K) :
    (wfMultialleleChain N K).expect (fun b => (b.val l : ℝ)) a = a.val l := by
  exact wfMultiallele_expect_count N K a l

end Rhone.MarkovChain
