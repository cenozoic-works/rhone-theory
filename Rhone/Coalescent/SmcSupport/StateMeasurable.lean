/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.MaterialMeasurable
public import Rhone.Coalescent.FiniteIntervalMaterialSuccessorMeas
public import Rhone.Coalescent.SmcSupport.StateSupport

/-! # State predicates are Borel on the dynamic finite-array state space -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

theorem statePredicate_measurable (P : State → Prop)
    (hP : ∀ m, MeasurableSet {p : FiberState m | P (stateOfFiber m p)}) :
    MeasurableSet {s : State | P s} := by
  have h : MeasurableSet {p : LiveState × (ℝ × ℕ) |
      P (p.2.1, p.2.2, p.1)} := by
    apply measurableSet_prod_sigma_of_fibers
    intro m
    exact (hP m).preimage
      (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  exact h.preimage
    (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))

theorem validState_measurable : MeasurableSet {s : State | Valid s} := by
  apply statePredicate_measurable
  intro m
  change MeasurableSet {p : FiberState m | 0 ≤ p.1 ∧
    (∀ i, MaterialValid (p.2.2 i).2) ∧
    (∀ i, (p.2.2 i).1 < p.2.1) ∧ Function.Injective (fun i => (p.2.2 i).1)}
  have ha (i : Fin m) : Measurable (fun p : FiberState m => p.2.2 i) :=
    (measurable_pi_apply i).comp measurable_snd.snd
  refine (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_forall _ (fun i => materialValid_measurable.preimage (ha i).snd)).inter
      ((measurableSet_forall _ (fun i =>
        measurableSet_lt (ha i).fst measurable_snd.fst)).inter ?_))
  change MeasurableSet {p : FiberState m | ∀ i j, (p.2.2 i).1 = (p.2.2 j).1 → i = j}
  apply measurableSet_forall
  intro i
  apply measurableSet_forall
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (ha i).fst (ha j).fst).compl

theorem allFull_measurable : MeasurableSet {s : State | AllMaterials FullAtoms s} := by
  apply statePredicate_measurable
  intro m
  change MeasurableSet {p : FiberState m | ∀ i, FullAtoms (p.2.2 i).2}
  apply measurableSet_forall
  intro i
  exact fullAtoms_measurable.preimage
    (((measurable_pi_apply i).comp measurable_snd.snd).snd)

theorem allContacts_measurable : MeasurableSet {s : State |
    ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2} := by
  apply statePredicate_measurable
  intro m
  change MeasurableSet {p : FiberState m | ∀ i j, touches (p.2.2 i).2 (p.2.2 j).2}
  have ha (i : Fin m) : Measurable (fun p : FiberState m => (p.2.2 i).2) :=
    ((measurable_pi_apply i).comp measurable_snd.snd).snd
  apply measurableSet_forall
  intro i
  apply measurableSet_forall
  intro j
  exact (measurableSet_le (hullLo_measurable.comp (ha i))
    (hullHi_measurable.comp (ha j))).inter
      (measurableSet_le (hullLo_measurable.comp (ha j)) (hullHi_measurable.comp (ha i)))

end Rhone.Coalescent.SmcSupport
