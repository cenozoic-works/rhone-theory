/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LambdaRates
public import Rhone.Coalescent.PitmanConverse

/-!
# The converse of Pitman's consistency theorem for Λ-coalescent rates

Source: pitman1999, Section 3.1, Lemma 18, eq. (22). -/

@[expose] public section

namespace Rhone.Unproved

open MeasureTheory Set Coalescent
open scoped fwdDiff

/-- Source: hausdorff1921, Thm III, pp. 98–102. -/
theorem hausdorff_moment_existsUnique (m : ℕ → ℝ)
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) :
    ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, m n = ∫ x, x ^ n ∂μ :=
  Rhone.Analysis.HausdorffMoment.hausdorff_moment_existsUnique m hm

theorem lambdaRate_diag_eq_moment {Λ : Measure ℝ} (hΛ : Λ (Icc (0 : ℝ) 1)ᶜ = 0) (n : ℕ) :
    lambdaRate Λ (n + 2) (n + 2) = ∫ x, x ^ n ∂Λ :=
  Rhone.Coalescent.lambdaRate_diag_eq_moment hΛ n

/-- Source: pitman1999, Section 3.1, Lemma 18, eq. (22). -/
theorem lambdaRate_existsUnique_of_consistent (lam : ℕ → ℕ → ℝ)
    (hnn : ∀ b k : ℕ, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hrec : ∀ b k : ℕ, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1)) :
    ∃! Λ : Measure ℝ, IsFiniteMeasure Λ ∧ Λ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ b k : ℕ, 2 ≤ k → k ≤ b → lam b k = lambdaRate Λ b k :=
  Rhone.Coalescent.lambdaRate_existsUnique_of_consistent lam hnn hrec

end Rhone.Unproved
