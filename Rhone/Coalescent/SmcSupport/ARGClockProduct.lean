/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.MarkedEventRates

/-! # Factorization of chronological event-clock densities -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

noncomputable def argCoalExposure {n : ℕ} (s : Fin n → State)
    (δ : Fin n → ℝ) : ℝ :=
  ∑ j, ((s j).2.2.1 : ℝ) * (((s j).2.2.1 : ℝ) - 1) / 2 * δ j

noncomputable def argHullExposure {n : ℕ} (s : Fin n → State)
    (δ : Fin n → ℝ) : ℝ :=
  ∑ j, (∑ i, hullLength ((s j).2.2.2 i).2) * δ j

theorem argClockProduct_factorization {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (s : Fin n → State) (δ : Fin n → ℝ) :
    (∏ j, Real.exp (-(totalRate false R (s j) : ℝ) * δ j)) =
      Real.exp (-argCoalExposure s δ - R / 2 * argHullExposure s δ) := by
  rw [← Real.exp_sum]
  congr 1
  calc
    _ = ∑ j : Fin n,
        (-(((s j).2.2.1 : ℝ) * (((s j).2.2.1 : ℝ) - 1) / 2 * δ j) -
          R / 2 * ((∑ i, hullLength ((s j).2.2.2 i).2) * δ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [totalRate_unrestricted_real R hR]
      unfold recombinationRate
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, argCoalExposure, argHullExposure]

end Rhone.Coalescent.SmcSupport
