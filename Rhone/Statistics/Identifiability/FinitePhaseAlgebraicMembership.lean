/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseCDFWitness
public import Rhone.Statistics.Identifiability.FiniteExitNormalization

/-! # Fully finite algebraic pan-membership conditions, including normalization -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open ThreeSampleMembership ThreeSampleCDF
variable {n m : ℕ}

lemma mass_one_iff_linear_system (M : Model n m) :
    M.law univ = 1 ↔ ∃ β : Fin (n + m) → ℝ, β ᵥ* M.N = M.γ := by
  have he : WeightedExit.law M.N M.γ univ = M.law univ := by
    rw [← M.root_marginal, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
  rw [← he]
  exact WeightedExit.mass_one_iff_rowSpace M.N M.γ M.N_metzler M.N_rows M.γ_nonnegative M.γ_sum

lemma probability_iff_linear_system (M : Model n m) :
    IsProbabilityMeasure M.law ↔ ∃ β : Fin (n + m) → ℝ, β ᵥ* M.N = M.γ := by
  rw [← M.mass_one_iff_linear_system]
  exact ⟨fun h => h.measure_univ, fun h => ⟨h⟩⟩

variable [NeZero n] [NeZero m]

theorem pan_representable_iff_finite_algebra (M : Model n m) :
    PanRepresentable M.law ↔
      (∃ β : Fin (n + m) → ℝ, β ᵥ* M.N = M.γ) ∧ M.Certificate := by
  rw [M.pan_representable_iff_mass_and_certificate, M.mass_one_iff_linear_system]

theorem pan_representable_iff_kernel_and_certificate (M : Model n m) :
    PanRepresentable M.law ↔
      (∀ w : Fin (n + m) → ℝ, M.N *ᵥ w = 0 → dotProduct M.γ w = 0) ∧ M.Certificate := by
  rw [M.pan_representable_iff_finite_algebra, finite_rowSpace_iff_annihilates_kernel]

theorem cdf_witness_of_linear_and_certificate_failure (M : Model n m)
    (hnorm : ∃ β : Fin (n + m) → ℝ, β ᵥ* M.N = M.γ) (hc : ¬M.Certificate) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ rootFreeStatistic M.law s t ≠ 0 := by
  let : IsProbabilityMeasure M.law := M.probability_iff_linear_system.mpr hnorm
  exact M.exists_rootFreeStatistic_ne_zero hc

end Rhone.Statistics.Identifiability.FinitePhase.Model
