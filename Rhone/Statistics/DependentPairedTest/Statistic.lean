/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProbability

/-! # The fixed self-normalized rule; no source parameter is an input -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest

noncomputable def sumStatistic {N : ℕ} (z : Fin N → ℝ) : ℝ := ∑ i, z i

noncomputable def squareStatistic {N : ℕ} (z : Fin N → ℝ) : ℝ := ∑ i, (z i)^2

def Rejects {N : ℕ} (z : Fin N → ℝ) : Prop :=
  0 < squareStatistic z ∧ 20 * squareStatistic z ≤ (sumStatistic z)^2

end Rhone.Statistics.DependentPairedTest
