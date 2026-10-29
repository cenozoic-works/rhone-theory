/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Rhone.Coalescent.FiniteIntervalMaterialState
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic.FunProp
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Concrete next-event mark law for the finite-interval material arrays -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open scoped BigOperators
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Ioo 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform, Real.volume_Ioo]

abbrev ActionIndex (s : State) :=
  (Fin s.2.2.1 × Fin s.2.2.1) ⊕ Fin s.2.2.1

noncomputable def candidateRate (mode : Mode) (R : ℝ) (s : State) : ActionIndex s → ℝ≥0 := by
  classical
  exact fun
  | .inl ij => if ij.1.val < ij.2.val ∧
      (mode = false ∨ touches (s.2.2.2 ij.1).2 (s.2.2.2 ij.2).2) then 1 else 0
  | .inr i => R.toNNReal / 2 * ⟨hullLength (s.2.2.2 i).2, le_max_left _ _⟩

noncomputable def totalRate (mode : Mode) (R : ℝ) (s : State) : ℝ≥0 :=
  ∑ a : ActionIndex s, candidateRate mode R s a

noncomputable def candidateLaw (s : State) : ActionIndex s → Measure Event
  | .inl ij => Measure.dirac (.inr (.inl (ij.1.val, ij.2.val)))
  | .inr i => unitUniform.map (fun u => .inr (.inr
      (i.val, hullLo (s.2.2.2 i).2 + hullLength (s.2.2.2 i).2 * u)))

instance candidateLaw_probability (s : State) (a : ActionIndex s) :
    IsProbabilityMeasure (candidateLaw s a) := by
  cases a with
  | inl ij => unfold candidateLaw; infer_instance
  | inr i =>
    unfold candidateLaw
    infer_instance

noncomputable def rawMarkedLaw (mode : Mode) (R : ℝ) (s : State) : Measure Event :=
  ∑ a : ActionIndex s, (candidateRate mode R s a : ℝ≥0∞) • candidateLaw s a

theorem rawMarkedLaw_univ (mode : Mode) (R : ℝ) (s : State) :
    rawMarkedLaw mode R s Set.univ = (totalRate mode R s : ℝ≥0∞) := by
  simp [rawMarkedLaw, totalRate]

noncomputable def markedLaw (mode : Mode) (R : ℝ) (s : State) : Measure Event :=
  if s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0 then Measure.dirac (.inl ())
  else (totalRate mode R s : ℝ≥0∞)⁻¹ • rawMarkedLaw mode R s

instance markedLaw_probability (mode : Mode) (R : ℝ) (s : State) :
    IsProbabilityMeasure (markedLaw mode R s) := by
  classical
  unfold markedLaw
  split_ifs with h
  · infer_instance
  · constructor
    rw [Measure.smul_apply, rawMarkedLaw_univ, smul_eq_mul]
    apply ENNReal.inv_mul_cancel
    · exact_mod_cast (show totalRate mode R s ≠ 0 from fun hz => h (Or.inr hz))
    · exact ENNReal.coe_ne_top

def splitSet : Set Event := {e | match e with
  | .inr (.inr _) => True
  | _ => False}

def coalSet : Set Event := {e | match e with
  | .inr (.inl _) => True
  | _ => False}

theorem splitSet_measurable : MeasurableSet splitSet := by
  have heq : splitSet = Sum.inr '' (Sum.inr '' (Set.univ : Set (ℕ × ℝ))) := by
    ext e
    cases e with
    | inl u => simp [splitSet]
    | inr e => cases e <;> simp [splitSet]
  rw [heq]
  exact MeasurableSet.univ.inr_image.inr_image

theorem coalSet_measurable : MeasurableSet coalSet := by
  have heq : coalSet = Sum.inr '' (Sum.inl '' (Set.univ : Set (ℕ × ℕ))) := by
    ext e
    cases e with
    | inl u => simp [coalSet]
    | inr e => cases e <;> simp [coalSet]
  rw [heq]
  exact MeasurableSet.univ.inl_image.inr_image

theorem candidateLaw_split_mass (s : State) (a : ActionIndex s) :
    candidateLaw s a splitSet = match a with | .inl _ => 0 | .inr _ => 1 := by
  cases a with
  | inl ij =>
    rw [candidateLaw, Measure.dirac_apply' _ splitSet_measurable]
    simp [splitSet]
  | inr i =>
    rw [candidateLaw, Measure.map_apply (by fun_prop) splitSet_measurable]
    simp [splitSet]

theorem candidateLaw_coal_mass (s : State) (a : ActionIndex s) :
    candidateLaw s a coalSet = match a with | .inl _ => 1 | .inr _ => 0 := by
  cases a with
  | inl ij =>
    rw [candidateLaw, Measure.dirac_apply' _ coalSet_measurable]
    simp [coalSet]
  | inr i =>
    rw [candidateLaw, Measure.map_apply (by fun_prop) coalSet_measurable]
    simp [coalSet]

noncomputable def splitRate (R : ℝ) (s : State) : ℝ≥0 :=
  ∑ i : Fin s.2.2.1, candidateRate false R s (.inr i)

noncomputable def coalRate (mode : Mode) (s : State) : ℝ≥0 :=
  ∑ ij : Fin s.2.2.1 × Fin s.2.2.1, candidateRate mode 0 s (.inl ij)

theorem candidateRate_split_eq (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (s : State) (i : Fin s.2.2.1) :
    (candidateRate mode R s (.inr i) : ℝ) = R / 2 * hullLength (s.2.2.2 i).2 := by
  change (R.toNNReal : ℝ) / 2 * hullLength (s.2.2.2 i).2 = _
  rw [Real.coe_toNNReal R hR]

theorem totalRate_eq (mode : Mode) (R : ℝ) (s : State) :
    totalRate mode R s = coalRate mode s + splitRate R s := by
  simp [totalRate, Fintype.sum_sum_type, coalRate, splitRate, candidateRate]

theorem rawMarkedLaw_split_mass (mode : Mode) (R : ℝ) (s : State) :
    rawMarkedLaw mode R s splitSet = (splitRate R s : ℝ≥0∞) := by
  classical
  unfold rawMarkedLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, candidateLaw_split_mass]
  rw [Fintype.sum_sum_type]
  simp [splitRate, candidateRate]

theorem rawMarkedLaw_coal_mass (mode : Mode) (R : ℝ) (s : State) :
    rawMarkedLaw mode R s coalSet = (coalRate mode s : ℝ≥0∞) := by
  classical
  unfold rawMarkedLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, candidateLaw_coal_mass]
  rw [Fintype.sum_sum_type]
  simp only [mul_one, mul_zero, Finset.sum_const_zero, add_zero]
  change (∑ ij : Fin s.2.2.1 × Fin s.2.2.1,
    (candidateRate mode 0 s (.inl ij) : ℝ≥0∞)) = (coalRate mode s : ℝ≥0∞)
  simp [coalRate]

theorem markedLaw_split_mass (mode : Mode) (R : ℝ) (s : State)
    (hm : 1 < s.2.2.1) (hr : totalRate mode R s ≠ 0) :
    markedLaw mode R s splitSet =
      (splitRate R s : ℝ≥0∞) / (totalRate mode R s : ℝ≥0∞) := by
  rw [markedLaw, ite_eq_right (not_or.mpr ⟨Nat.not_le.mpr hm, hr⟩),
    Measure.smul_apply, rawMarkedLaw_split_mass,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem markedLaw_coal_mass (mode : Mode) (R : ℝ) (s : State)
    (hm : 1 < s.2.2.1) (hr : totalRate mode R s ≠ 0) :
    markedLaw mode R s coalSet =
      (coalRate mode s : ℝ≥0∞) / (totalRate mode R s : ℝ≥0∞) := by
  rw [markedLaw, ite_eq_right (not_or.mpr ⟨Nat.not_le.mpr hm, hr⟩),
    Measure.smul_apply, rawMarkedLaw_coal_mass,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

noncomputable def holdingLaw (mode : Mode) (R : ℝ) (s : State) : Measure ℝ :=
  if s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0 then Measure.dirac 0
  else unitUniform.map (fun u => -Real.log u / (totalRate mode R s : ℝ))

instance holdingLaw_probability (mode : Mode) (R : ℝ) (s : State) :
    IsProbabilityMeasure (holdingLaw mode R s) := by
  classical
  unfold holdingLaw
  split_ifs
  · infer_instance
  · infer_instance

noncomputable def timedMarkedLaw (mode : Mode) (R : ℝ) (s : State) :
    Measure (ℝ × Event) :=
  (holdingLaw mode R s).prod (markedLaw mode R s)

instance timedMarkedLaw_probability (mode : Mode) (R : ℝ) (s : State) :
    IsProbabilityMeasure (timedMarkedLaw mode R s) := by
  unfold timedMarkedLaw
  infer_instance

end Rhone.Coalescent.IntervalProcess
