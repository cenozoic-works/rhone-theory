/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Rhone.Probability.ExplicitFormula.Defs
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

/-! # The executable centred source -/

@[expose] public section

namespace Rhone.Computation

private theorem guardedYield (coef : Nat) (acc scale value : Rat) :
    (if coef > 0 then (pure (ForInStep.yield
      (acc + (coef : Rat) * scale * value)) : Id (ForInStep Rat))
      else pure (ForInStep.yield acc)) =
      pure (ForInStep.yield (acc + (coef : Rat) * scale * value)) := by
  by_cases h : 0 < coef
  · simp [h]
  · have hz : coef = 0 := by omega
    simp [hz]

theorem source_eq_srcR (p : Params) (tab : PhiTable) (i j t : Nat) :
    source p tab i j t = Rhone.Probability.ExplicitFormula.srcR
      (p.piA.getD 0 0 * p.piA.getD 1 0)
      (p.piA.getD 1 0 - p.piA.getD 0 0)
      (p.piB.getD 0 0 * p.piB.getD 1 0)
      (p.piB.getD 1 0 - p.piB.getD 0 0) tab.get i j t := by
  simp only [source, guardedYield]
  simp [Rhone.Probability.ExplicitFormula.srcR, Nat.cast_mul]
  ring

end Rhone.Computation
