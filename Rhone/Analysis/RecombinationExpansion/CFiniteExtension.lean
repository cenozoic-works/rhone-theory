/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.CFinite
public import Mathlib.Tactic.LinearCombination

/-! # C-finiteness of a sequence extended by finitely many terms -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open Polynomial

variable {F : Type*} [CommRing F]

theorem cfinite_step {M : ℕ} (D : Polynomial F) (G : PowerSeries F) {k : ℕ}
    (h : ∑ m ∈ Finset.range (M + 1), D.coeff (M - m) * PowerSeries.coeff (k - m) G = 0) :
    D.coeff M * PowerSeries.coeff k G
      = -∑ m ∈ Finset.range M, D.coeff (M - (m + 1)) * PowerSeries.coeff (k - (m + 1)) G := by
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.sub_zero] at h
  linear_combination h

theorem cfinite_ext {M : ℕ} (D : Polynomial F) (hlead : IsUnit (D.coeff M))
    (G G' : PowerSeries F)
    (hG : ∀ k, M < k → ∑ m ∈ Finset.range (M + 1),
      D.coeff (M - m) * PowerSeries.coeff (k - m) G = 0)
    (hG' : ∀ k, M < k → ∑ m ∈ Finset.range (M + 1),
      D.coeff (M - m) * PowerSeries.coeff (k - m) G' = 0)
    (hagree : ∀ r, r ≤ M → PowerSeries.coeff r G = PowerSeries.coeff r G') :
    G = G' := by
  refine PowerSeries.ext fun k => ?_
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge M k with hkM | hkM
    · have hstep := cfinite_step D G (hG k hkM)
      have hstep' := cfinite_step D G' (hG' k hkM)
      have hsum : (∑ m ∈ Finset.range M,
            D.coeff (M - (m + 1)) * PowerSeries.coeff (k - (m + 1)) G)
          = ∑ m ∈ Finset.range M,
            D.coeff (M - (m + 1)) * PowerSeries.coeff (k - (m + 1)) G' :=
        Finset.sum_congr rfl fun m hm => by
          rw [Finset.mem_range] at hm
          rw [ih (k - (m + 1)) (by omega)]
      have hmul : D.coeff M * PowerSeries.coeff k G = D.coeff M * PowerSeries.coeff k G' := by
        rw [hstep, hstep', hsum]
      exact hlead.mul_left_cancel hmul
    · exact hagree k hkM

theorem cfinite_ext_of_ne_zero {K : Type*} [Field K] {M : ℕ} (D : Polynomial K)
    (hlead : D.coeff M ≠ 0) (G G' : PowerSeries K)
    (hG : ∀ k, M < k → ∑ m ∈ Finset.range (M + 1),
      D.coeff (M - m) * PowerSeries.coeff (k - m) G = 0)
    (hG' : ∀ k, M < k → ∑ m ∈ Finset.range (M + 1),
      D.coeff (M - m) * PowerSeries.coeff (k - m) G' = 0)
    (hagree : ∀ r, r ≤ M → PowerSeries.coeff r G = PowerSeries.coeff r G') :
    G = G' :=
  cfinite_ext D (isUnit_iff_ne_zero.2 hlead) G G' hG hG' hagree

end Rhone.Analysis.RecombinationExpansion
