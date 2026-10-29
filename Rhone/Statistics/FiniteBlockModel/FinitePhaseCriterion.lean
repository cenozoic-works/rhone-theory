/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteBlockModel.OrderedCriterion
public import Rhone.Statistics.Identifiability.IntegrablePhaseMembership

/-! # Finite locally-integrable two-stage model endpoint -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.FiniteBlockModel
open WeakRegularSeparation Algebra.Identifiability MarkovChain.Identifiability Identifiability

theorem finitePhase_uniformlySeparated_iff {n m : ℕ} (M : IntegrablePhase.History n m)
    [IsProbabilityMeasure M.law] {k : ℝ} (hk : 0 < k) :
    UniformlySeparated k (uniformLift (durations M.law)) ↔ ¬M.DensityIdentity := by
  rw [ordered_uniformlySeparated_iff hk M.law M.ordered_support
    M.firstProfile M.firstProfile_matches, M.pan_representable_iff_density_identity]

end Rhone.Statistics.FiniteBlockModel
