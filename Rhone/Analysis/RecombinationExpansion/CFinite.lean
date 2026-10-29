/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Reverse

/-! # C-finiteness of the `1/ρ` coefficient sequence -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open Polynomial

variable {F : Type*} [CommRing F]

theorem cfinite_aux {M : ℕ} (Nt Dt : Polynomial F) (hN : Nt.natDegree ≤ M)
    (hD : Dt.natDegree ≤ M) (G : PowerSeries F)
    (h : (Nt : PowerSeries F) = (Dt : PowerSeries F) * G) {k : ℕ} (hk : M < k) :
    ∑ m ∈ Finset.range (M + 1), Dt.coeff m * PowerSeries.coeff (k - m) G = 0 := by
  have h0 : PowerSeries.coeff k (Nt : PowerSeries F) = 0 := by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h0
  simp only [Polynomial.coeff_coe] at h0
  rw [← h0]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    have hxM : M < x := by
      by_contra hc
      exact hx (Finset.mem_range.2 (by omega))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem cfinite_recurrence {M : ℕ} (N D : Polynomial F) (hN : N.natDegree ≤ M)
    (hD : D.natDegree ≤ M) (G : PowerSeries F)
    (h : ((N.reflect M : Polynomial F) : PowerSeries F)
      = ((D.reflect M : Polynomial F) : PowerSeries F) * G) {k : ℕ} (hk : M < k) :
    ∑ m ∈ Finset.range (M + 1), D.coeff (M - m) * PowerSeries.coeff (k - m) G = 0 := by
  have key := cfinite_aux (N.reflect M) (D.reflect M)
    (le_trans natDegree_reflect_le (max_le (le_refl M) hN))
    (le_trans natDegree_reflect_le (max_le (le_refl M) hD)) G h hk
  rw [← key]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_reflect, revAt_le (by omega)]

end Rhone.Analysis.RecombinationExpansion
