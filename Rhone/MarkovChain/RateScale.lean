/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.JumpHold

/-! # Positive scaling of a finite generator -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace Rhone.MarkovChain.RateChain
variable {S : Type*} [Fintype S] [DecidableEq S] (R : Rhone.MarkovChain.RateChain S)

def scaled (c : ℝ) (hc : 0 < c) : Rhone.MarkovChain.RateChain S where
  Q x y := c * R.Q x y
  off_diag_nonneg x y h := mul_nonneg hc.le (R.off_diag_nonneg x y h)
  row_sum x := by rw [← Finset.mul_sum, R.row_sum, mul_zero]

omit [DecidableEq S] in
theorem scaled_rate (c : ℝ) (hc : 0 < c) (x : S) :
    (R.scaled c hc).rate x = c * R.rate x := by
  simp [scaled, rate]

theorem scaled_jumpMatrix (c : ℝ) (hc : 0 < c) :
    (R.scaled c hc).jumpMatrix = R.jumpMatrix := by
  funext x y
  simp only [jumpMatrix, scaled_rate]
  by_cases hx : R.rate x = 0
  · simp [hx]
  · simp only [mul_eq_zero, hc.ne', hx, or_self, ↓reduceIte]
    split_ifs
    · rfl
    · change c * R.Q x y / (c * R.rate x) = R.Q x y / R.rate x
      field_simp

theorem scaled_jumpChain (c : ℝ) (hc : 0 < c) :
    (R.scaled c hc).jumpChain = R.jumpChain := by
  simp only [jumpChain, scaled_jumpMatrix]

omit [DecidableEq S] in
theorem scaled_holdTime (c : ℝ) (hc : 0 < c)
    (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) :
    (R.scaled c hc).holdTime p k = R.holdTime p k / c := by
  simp only [holdTime, scaled_rate]
  ring

theorem scaled_costBefore (c : ℝ) (hc : 0 < c) (A : Finset S) (g : S → ℝ)
    (p : (ℕ → S) × (ℕ → ℝ)) :
    (R.scaled c hc).costBefore A g p =
      ENNReal.ofReal (1 / c) * R.costBefore A g p := by
  simp only [costBefore, scaled_holdTime]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext k
  split_ifs
  · simp
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
theorem scaled_jumpHoldLaw (c : ℝ) (hc : 0 < c) (x : S) :
    (R.scaled c hc).jumpHoldLaw x = R.jumpHoldLaw x := by
  simp only [jumpHoldLaw, scaled_jumpChain]

end Rhone.MarkovChain.RateChain
