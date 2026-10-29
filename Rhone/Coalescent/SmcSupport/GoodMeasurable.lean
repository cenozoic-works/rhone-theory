/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.GoodState
public import Rhone.Coalescent.SmcSupport.StateMeasurable

/-! # The capped-phase structural invariant is a Borel event -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

theorem good_measurable : MeasurableSet {z : TrackedState | Good z} := by
  have hc : MeasurableSet {z : TrackedState | 1 ≤ z.1.2.2.1} :=
    measurableSet_le measurable_const (liveCount_measurable.comp measurable_fst)
  have hz : MeasurableSet {z : TrackedState |
      Valid z.1 ∧ AllMaterials FullAtoms z.1 ∧ 1 ≤ z.1.2.2.1} :=
    (validState_measurable.preimage measurable_fst).inter
      ((allFull_measurable.preimage measurable_fst).inter hc)
  have ho : MeasurableSet {z : TrackedState | Valid z.1 ∧
      (∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) ∧ 1 ≤ z.1.2.2.1} :=
    (validState_measurable.preimage measurable_fst).inter
      ((allContacts_measurable.preimage measurable_fst).inter hc)
  have hp (p : Phase) : MeasurableSet {z : TrackedState | z.2.1 = p} :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  have he : {z : TrackedState | Good z} =
      ({z | z.2.1 = .zero} ∩ {z | Valid z.1 ∧ AllMaterials FullAtoms z.1 ∧ 1 ≤ z.1.2.2.1}) ∪
      ({z | z.2.1 = .one} ∩ {z | Valid z.1 ∧
        (∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) ∧ 1 ≤ z.1.2.2.1}) ∪
      {z | z.2.1 = .two} := by
    ext z
    cases h : z.2.1 <;> simp [Good, h]
  rw [he]
  exact (((hp .zero).inter hz).union ((hp .one).inter ho)).union (hp .two)

end Rhone.Coalescent.SmcSupport
