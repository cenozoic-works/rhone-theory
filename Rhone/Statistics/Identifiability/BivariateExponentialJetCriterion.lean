/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteExponentialJetCriterion
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # A finite rectangular jet certificate for any finite bivariate linear realization -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

def evaluateRight (L : Matrix ι ι ℝ →L[ℝ] (Matrix κ κ ℝ →L[ℝ] ℝ))
    (Y : Matrix κ κ ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ Y).comp L

lemma bivariate_zero_of_finite (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (L : Matrix ι ι ℝ →L[ℝ] (Matrix κ κ ℝ →L[ℝ] ℝ))
    (hzero : ∀ i : ℕ, i < Fintype.card ι → ∀ j : ℕ, j < Fintype.card κ →
      L (A ^ i) (B ^ j) = 0) (s t : ℝ) :
    L (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) = 0 := by
  have hpre : ∀ i : ℕ, i < Fintype.card ι →
      evaluateRight L (NormedSpace.exp (t • B)) (A ^ i) = 0 := by
    intro i hi
    exact exp_zero_of_finite B (L (A ^ i)) (hzero i hi) t
  exact exp_zero_of_finite A (evaluateRight L (NormedSpace.exp (t • B))) hpre s

theorem positive_bivariate_zero_iff_finite (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (L : Matrix ι ι ℝ →L[ℝ] (Matrix κ κ ℝ →L[ℝ] ℝ)) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      L (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) = 0) ↔
    (∀ i : ℕ, i < Fintype.card ι → ∀ j : ℕ, j < Fintype.card κ →
      L (A ^ i) (B ^ j) = 0) := by
  constructor
  · intro h i hi j hj
    have hpost : ∀ t : ℝ, 0 < t → L (A ^ i) (NormedSpace.exp (t • B)) = 0 := by
      intro t ht
      have hpre : ∀ s : ℝ, 0 < s →
          evaluateRight L (NormedSpace.exp (t • B)) (NormedSpace.exp (s • A)) = 0 := by
        intro s hs
        exact h s t hs ht
      exact (positive_exp_zero_iff_finite A
        (evaluateRight L (NormedSpace.exp (t • B)))).mp hpre i hi
    exact (positive_exp_zero_iff_finite B (L (A ^ i))).mp hpost j hj
  · intro h s t _ _
    exact bivariate_zero_of_finite A B L h s t

end Rhone.Statistics.Identifiability.FiniteExponentialJets
