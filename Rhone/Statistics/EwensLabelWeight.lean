/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KillPatternWeight

/-!
# Label weights of partitions for the Ewens urn

Source: ewens1972, eq. (A3), p. 107. -/

@[expose] public section
namespace Rhone.Statistics
open Finset

variable {τ : Type*} [DecidableEq τ]

noncomputable def labelWeight (θ : ℝ) (M : Multiset τ) : ℝ :=
  θ ^ M.toFinset.card * (∏ t ∈ M.toFinset, ((M.count t - 1).factorial : ℝ)) /
    ∏ i ∈ range M.card, (θ + (i : ℝ))

theorem labelWeight_zero (θ : ℝ) : labelWeight θ (0 : Multiset τ) = 1 := by
  simp [labelWeight]

theorem labelWeight_cons_of_notMem {θ : ℝ} (hθ : 0 < θ) {t : τ} {M : Multiset τ}
    (ht : t ∉ M) :
    labelWeight θ (t ::ₘ M) * (θ + (M.card : ℝ)) = θ * labelWeight θ M := by
  have hR : (∏ i ∈ range M.card, (θ + (i : ℝ))) ≠ 0 :=
    (Finset.prod_pos fun i _ => by positivity).ne'
  have hq : θ + (M.card : ℝ) ≠ 0 := by positivity
  have htf : t ∉ M.toFinset := fun h => ht (Multiset.mem_toFinset.1 h)
  have hprod : ∏ s ∈ M.toFinset, (((t ::ₘ M).count s - 1).factorial : ℝ) =
      ∏ s ∈ M.toFinset, ((M.count s - 1).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [Multiset.count_cons_of_ne (by rintro rfl; exact htf hs)]
  unfold labelWeight
  rw [Multiset.toFinset_cons, Finset.card_insert_of_notMem htf, Finset.prod_insert htf,
    Multiset.count_cons_self, Multiset.count_eq_zero_of_notMem ht, hprod, Multiset.card_cons,
    Finset.prod_range_succ]
  simp only [zero_add, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
  field_simp
  ring

theorem labelWeight_cons_of_mem {θ : ℝ} (hθ : 0 < θ) {t : τ} {M : Multiset τ} (ht : t ∈ M) :
    labelWeight θ (t ::ₘ M) * (θ + (M.card : ℝ)) = (M.count t : ℝ) * labelWeight θ M := by
  have hR : (∏ i ∈ range M.card, (θ + (i : ℝ))) ≠ 0 :=
    (Finset.prod_pos fun i _ => by positivity).ne'
  have hq : θ + (M.card : ℝ) ≠ 0 := by positivity
  have htf : t ∈ M.toFinset := Multiset.mem_toFinset.2 ht
  have hc : 0 < M.count t := Multiset.count_pos.2 ht
  have hprod : ∏ s ∈ M.toFinset, (((t ::ₘ M).count s - 1).factorial : ℝ) =
      (M.count t : ℝ) * ∏ s ∈ M.toFinset, ((M.count s - 1).factorial : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ htf, ← Finset.mul_prod_erase _ _ htf, ← mul_assoc]
    congr 1
    · rw [Multiset.count_cons_self, Nat.add_sub_cancel, ← Nat.cast_mul,
        Nat.mul_factorial_pred hc.ne']
    · refine Finset.prod_congr rfl fun s hs => ?_
      rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hs)]
  unfold labelWeight
  rw [Multiset.toFinset_cons, Finset.insert_eq_of_mem htf, hprod, Multiset.card_cons,
    Finset.prod_range_succ]
  field_simp

end Rhone.Statistics
