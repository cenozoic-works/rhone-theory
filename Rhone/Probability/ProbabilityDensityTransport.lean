/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ProbabilityPermutationTransport
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Weighted domination after exact marked-coordinate transport -/

@[expose] public section
namespace Rhone.Probability.MeasureTransport
open MeasureTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]

theorem markedPermutation_density_le (n : ℕ) (A : Set (α × MarkedClocks n))
    (hA : MeasurableSet A) (F : α × MarkedClocks n → β × MarkedClocks n)
    (hF : Measurable F) (hinj : Set.InjOn F A)
    (hdistinct : ∀ z ∈ A, Function.Injective z.2.1)
    (hperm : ∀ z ∈ A, ∃ p : Equiv.Perm (Fin n), (F z).2 = clockPermutation p z.2)
    (f : α × MarkedClocks n → ℝ≥0∞) (g : β × MarkedClocks n → ℝ≥0∞)
    (hg : Measurable g) (hfg : ∀ z ∈ A, f z ≤ g (F z)) :
    ((((Measure.count : Measure α).prod volume).restrict A).withDensity f).map F ≤
      ((Measure.count : Measure β).prod volume).withDensity g := by
  let μ : Measure (α × MarkedClocks n) :=
    ((Measure.count : Measure α).prod volume).restrict A
  let ν : Measure (β × MarkedClocks n) := (Measure.count : Measure β).prod volume
  obtain ⟨_, hmap⟩ := markedPermutation_transport n A hA F hF hinj hdistinct hperm
  have hle : μ.map F ≤ ν := by
    rw [show μ.map F = ν.restrict (F '' A) from hmap]
    exact Measure.restrict_le_self
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply hF hB, withDensity_apply _ (hF hB), withDensity_apply _ hB]
  calc
    ∫⁻ z in F ⁻¹' B, f z ∂μ ≤ ∫⁻ z in F ⁻¹' B, g (F z) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem hA)] with z hz
      exact hfg z hz
    _ = ∫⁻ z in B, g z ∂μ.map F := (setLIntegral_map hB hg hF).symm
    _ ≤ ∫⁻ z in B, g z ∂ν := lintegral_mono' (Measure.restrict_mono le_rfl hle) le_rfl

end Rhone.Probability.MeasureTransport
