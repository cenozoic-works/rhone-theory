/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.Table
public import Rhone.Statistics.ConcretePatternMoments.Data

/-! # Exact 95 integer coefficient identities; ordinary kernel reduction only -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments

def targetNumerator : Fin 5 → Fin 19 → ℤ :=
  ![![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1], ![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem moment_coefficient_certificate (i : Fin 5) (j : Fin 19) :
    (∑ r : Row, (multiplicityNat r.1 * multiplicityNat r.2.1 *
      multiplicityNat r.2.2 : ℤ) * numerator i r * coefficient r j) =
        63700992 * targetNumerator i j := by
  fin_cases i <;> fin_cases j <;> decide

end Rhone.Statistics.ConcreteBettingFeatures
