/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.ScoreDifference

/-! # The source-centred gradient and the localization margin -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.LocalizedBetting
open ThreeSiteRobustness ThreeSiteSeparator

def gradient (s : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-14220 - 104580 * (s 0 - 1 / 3) - 48090 * (s 2 - 1 / 7),
    41160 + 154350 * (s 1 - 1 / 5), -32060 - 48090 * (s 0 - 1 / 3), 99540, -102900]

def contrast (s v : Fin 5 → ℝ) : ℝ := ∑ i, gradient s i * (v i - s i)

theorem exact_taylor (s v : Fin 5 → ℝ) :
    scoreVector v = scoreVector s + contrast s v - 52290 * (v 0 - s 0) ^ 2 -
      48090 * (v 0 - s 0) * (v 2 - s 2) + 77175 * (v 1 - s 1) ^ 2 := by
  simp [scoreVector, score, linearScore, contrast, gradient, Fin.sum_univ_succ]
  ring

theorem local_null_margin (s v : Fin 5 → ℝ) {eps : ℝ} (heps : 0 ≤ eps)
    (h0 : |v 0 - s 0| ≤ 2 * eps) (h2 : |v 2 - s 2| ≤ 2 * eps)
    (hnull : scoreVector v ≤ 0) :
    contrast s v + (scoreVector s - 401520 * eps ^ 2) ≤ 0 := by
  have hs : |v 0 - s 0| ^ 2 ≤ (2 * eps) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h0
  rw [sq_abs] at hs
  have hp : (v 0 - s 0) * (v 2 - s 2) ≤ (2 * eps) * (2 * eps) := by
    calc
      _ ≤ |(v 0 - s 0) * (v 2 - s 2)| := le_abs_self _
      _ = |v 0 - s 0| * |v 2 - s 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul h0 h2 (abs_nonneg _) (by positivity)
  have ht := exact_taylor s v
  nlinarith [sq_nonneg (v 1 - s 1)]

theorem centered_contrast (s : Fin 5 → ℝ) : contrast s s = 0 := by
  simp [contrast]

end Rhone.Statistics.LocalizedBetting
