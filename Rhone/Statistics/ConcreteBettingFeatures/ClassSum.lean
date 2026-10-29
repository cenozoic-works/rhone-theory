/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.Table

/-! # Weighted finite-class aggregation, independent of numerical source values -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments

def rowMultiplicity (r : Row) : ℕ :=
  multiplicityNat r.1 * multiplicityNat r.2.1 * multiplicityNat r.2.2

theorem weighted_class_sum (f : Fin 14 → ℝ) :
    (∑ r : Row, (rowMultiplicity r : ℝ) * f (rowClass r)) =
      ∑ c : Fin 14, (∑ r : Row with rowClass r = c, (rowMultiplicity r : ℝ)) * f c := by
  rw [← Finset.sum_fiberwise Finset.univ rowClass]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(Finset.mem_filter.mp hr).2]

theorem row_multiplicity_real (r : Row) :
    (rowMultiplicity r : ℝ) = ConcretePatternMoments.multiplicity r.1 *
      ConcretePatternMoments.multiplicity r.2.1 * ConcretePatternMoments.multiplicity r.2.2 := by
  simp only [rowMultiplicity, Nat.cast_mul, ConcretePatternMoments.multiplicity]

end Rhone.Statistics.ConcreteBettingFeatures
