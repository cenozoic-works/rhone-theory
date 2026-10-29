/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic.Linarith

/-! # Testing bounds from a common submeasure -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace Rhone.Statistics.Identifiability

variable {X : Type*} [MeasurableSpace X]

theorem real_apply_le_of_le {η μ : Measure X} [IsFiniteMeasure μ]
    (h : η ≤ μ) (A : Set X) : η.real A ≤ μ.real A :=
  ENNReal.toReal_mono (measure_ne_top μ A) (h A)

theorem error_sum_ge_common_mass {η μ ν : Measure X}
    [IsFiniteMeasure η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hημ : η ≤ μ) (hην : η ≤ ν) {A : Set X} (hA : MeasurableSet A) :
    η.real univ ≤ μ.real Aᶜ + ν.real A := by
  have hsum := measureReal_add_measureReal_compl (μ := η) hA
  have hcomp := real_apply_le_of_le hημ Aᶜ
  have hrejection := real_apply_le_of_le hην A
  linarith

theorem power_le_of_common_submeasure {η μ ν : Measure X}
    [IsFiniteMeasure η] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hημ : η ≤ μ) (hην : η ≤ ν) {A : Set X} (hA : MeasurableSet A)
    {α : ℝ} (hlevel : ν.real A ≤ α) :
    μ.real A ≤ α + 1 - η.real univ := by
  have herrors := error_sum_ge_common_mass hημ hην hA
  have hsum := measureReal_add_measureReal_compl (μ := μ) hA
  rw [probReal_univ] at hsum
  linarith

theorem pi_le_pi_of_le {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MeasurableSpace (Y i)] {η μ : (i : ι) → Measure (Y i)}
    [∀ i, SigmaFinite (η i)] (h : ∀ i, η i ≤ μ i) :
    Measure.pi η ≤ Measure.pi μ := by
  have ho : (Measure.pi η).toOuterMeasure ≤
      OuterMeasure.pi (fun i => (μ i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    change Measure.pi η (Set.pi univ s) ≤ ∏ i, μ i (s i)
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod (fun i _ => h i (s i))
  intro s
  calc
    Measure.pi η s ≤ OuterMeasure.pi (fun i => (μ i).toOuterMeasure) s := ho s
    _ ≤ Measure.pi μ s := by
      rw [Measure.pi]
      exact le_toMeasure_apply _ _ _

theorem iid_common_mass (η : Measure X) [IsFiniteMeasure η] (N : ℕ) :
    (Measure.pi (fun _ : Fin N => η)).real univ = (η.real univ) ^ N := by
  simp [Measure.real, Measure.pi_univ, ENNReal.toReal_pow]

theorem iid_error_sum_ge_common_mass {η μ ν : Measure X}
    [IsFiniteMeasure η] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hημ : η ≤ μ) (hην : η ≤ ν) (N : ℕ) {A : Set (Fin N → X)}
    (hA : MeasurableSet A) :
    (η.real univ) ^ N ≤
      (Measure.pi (fun _ : Fin N => μ)).real Aᶜ +
      (Measure.pi (fun _ : Fin N => ν)).real A := by
  have h := error_sum_ge_common_mass
    (pi_le_pi_of_le (fun _ : Fin N => hημ))
    (pi_le_pi_of_le (fun _ : Fin N => hην)) hA
  simpa only [iid_common_mass] using h

theorem iid_power_le_of_common_submeasure {η μ ν : Measure X}
    [IsFiniteMeasure η] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hημ : η ≤ μ) (hην : η ≤ ν) (N : ℕ) {A : Set (Fin N → X)}
    (hA : MeasurableSet A) {α : ℝ}
    (hlevel : (Measure.pi (fun _ : Fin N => ν)).real A ≤ α) :
    (Measure.pi (fun _ : Fin N => μ)).real A ≤
      α + 1 - (η.real univ) ^ N := by
  have h := power_le_of_common_submeasure
    (pi_le_pi_of_le (fun _ : Fin N => hημ))
    (pi_le_pi_of_le (fun _ : Fin N => hην)) hA hlevel
  simpa only [iid_common_mass] using h

theorem iid_common_mass_le_of_level_and_power {η μ ν : Measure X}
    [IsFiniteMeasure η] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hημ : η ≤ μ) (hην : η ≤ ν) (N : ℕ) {A : Set (Fin N → X)}
    (hA : MeasurableSet A) {α β : ℝ}
    (hlevel : (Measure.pi (fun _ : Fin N => ν)).real A ≤ α)
    (hpower : 1 - β ≤ (Measure.pi (fun _ : Fin N => μ)).real A) :
    (η.real univ) ^ N ≤ α + β := by
  have h := iid_power_le_of_common_submeasure hημ hην N hA hlevel
  linarith

end Rhone.Statistics.Identifiability
