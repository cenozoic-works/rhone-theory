/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialArrayOperations
public import Rhone.Coalescent.SmcSupport.Material

/-! # Borel sets for the material predicates of the good-state invariant -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

theorem measurableSet_sigma_of_fibers {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (P : Sigma β → Prop)
    (hP : ∀ i, MeasurableSet {a : β i | P ⟨i, a⟩}) :
    MeasurableSet {a : Sigma β | P a} := by
  change MeasurableSet[⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)] _
  exact MeasurableSpace.measurableSet_iInf.mpr hP

theorem measurableSet_forall {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (P : α → ι → Prop) (hP : ∀ i, MeasurableSet {a | P a i}) :
    MeasurableSet {a | ∀ i, P a i} := by
  have he : {a | ∀ i, P a i} = ⋂ i, {a | P a i} := by ext; simp
  rw [he]
  exact MeasurableSet.iInter hP

theorem measurableSet_exists {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (P : α → ι → Prop) (hP : ∀ i, MeasurableSet {a | P a i}) :
    MeasurableSet {a | ∃ i, P a i} := by
  have he : {a | ∃ i, P a i} = ⋃ i, {a | P a i} := by ext; simp
  rw [he]
  exact MeasurableSet.iUnion hP

theorem materialValid_measurable : MeasurableSet {a : Material | MaterialValid a} := by
  apply measurableSet_sigma_of_fibers
  intro k
  change MeasurableSet {a : Fin (k + 1) → ℝ × ℝ |
    (∀ i, 0 ≤ (a i).1 ∧ (a i).1 ≤ (a i).2 ∧ (a i).2 ≤ 1) ∧
    ∃ i, (a i).1 < (a i).2}
  apply MeasurableSet.inter
  · apply measurableSet_forall
    intro i
    have hl : Measurable (fun a : Fin (k + 1) → ℝ × ℝ => (a i).1) :=
      (measurable_pi_apply i).fst
    have hh : Measurable (fun a : Fin (k + 1) → ℝ × ℝ => (a i).2) :=
      (measurable_pi_apply i).snd
    exact (measurableSet_le measurable_const hl).inter
      ((measurableSet_le hl hh).inter (measurableSet_le hh measurable_const))
  · apply measurableSet_exists
    intro i
    exact measurableSet_lt (measurable_pi_apply i).fst (measurable_pi_apply i).snd

theorem fullAtoms_measurable : MeasurableSet {a : Material | FullAtoms a} := by
  apply measurableSet_sigma_of_fibers
  intro k
  change MeasurableSet {a : Fin (k + 1) → ℝ × ℝ | ∀ i, a i = (0, 1)}
  apply measurableSet_forall
  intro i
  exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const

theorem measurableSet_prod_sigma_of_fibers {ι : Type*} [Countable ι]
    {β : ι → Type*} {γ : Type*} [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    (P : Sigma β × γ → Prop)
    (hP : ∀ i, MeasurableSet {p : β i × γ | P (⟨i, p.1⟩, p.2)}) :
    MeasurableSet {p | P p} := by
  classical
  have hf : Measurable (fun p : Sigma β × γ => if P p then (1 : ℝ) else 0) := by
    apply measurable_prod_sigma_of_fibers
    intro i
    exact measurable_const.piecewise (hP i) measurable_const
  have he : {p : Sigma β × γ | P p} =
      {p | (if P p then (1 : ℝ) else 0) = 1} := by ext p; by_cases h : P p <;> simp [h]
  rw [he]
  exact measurableSet_eq_fun hf measurable_const

end Rhone.Coalescent.SmcSupport
