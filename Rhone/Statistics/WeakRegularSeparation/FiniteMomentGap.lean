/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.CompactPan

/-! # Finite moment gap outside the compact candidate family -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy

def monoMoment (n : Fin 3 → ℕ) (μ : ProbabilityMeasure (Cube 3)) : ℝ :=
  ∫ x, ∏ i, (x i).val ^ n i ∂(μ : Measure (Cube 3))

theorem mono_moment_continuous (n : Fin 3 → ℕ) : Continuous (monoMoment n) := by
  let f : C(Cube 3, ℝ) := ⟨fun x => ∏ i, (x i).val ^ n i, by fun_prop⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

theorem finite_moment_gap_of_outside (target : ProbabilityMeasure (Cube 3))
    (hout : target ∉ Set.range compactPan) :
    ∃ S : Finset (Fin 3 → ℕ), ∃ δ : ℝ, 0 < δ ∧
      ∀ μ : ProbabilityMeasure CompactTime,
        δ ≤ ∑ n ∈ S, |monoMoment n target - monoMoment n (compactPan μ)| := by
  classical
  let U (n : Fin 3 → ℕ) : Set (ProbabilityMeasure (Cube 3)) :=
    {ρ | 0 < |monoMoment n target - monoMoment n ρ|}
  have hU (n : Fin 3 → ℕ) : IsOpen (U n) :=
    isOpen_lt continuous_const ((continuous_const.sub (mono_moment_continuous n)).abs)
  have hcover : Set.range compactPan ⊆ ⋃ n, U n := by
    intro ρ hρ
    have hn : ∃ n : Fin 3 → ℕ, monoMoment n target ≠ monoMoment n ρ := by
      by_contra! he
      have heq : (target : Measure (Cube 3)) = ρ := compact_moment_unique 3 target ρ he
      have hprob : target = ρ := ProbabilityMeasure.toMeasure_injective heq
      exact hout (hprob ▸ hρ)
    obtain ⟨n, hn⟩ := hn
    exact mem_iUnion.mpr ⟨n, abs_pos.mpr (sub_ne_zero.mpr hn)⟩
  obtain ⟨S, hS⟩ := compact_pan_range_compact.elim_finite_subcover U hU hcover
  let D (ρ : ProbabilityMeasure (Cube 3)) : ℝ :=
    ∑ n ∈ S, |monoMoment n target - monoMoment n ρ|
  have hD : Continuous D := by
    apply continuous_finsetSum
    intro n _
    exact (continuous_const.sub (mono_moment_continuous n)).abs
  have hpos (ρ : ProbabilityMeasure (Cube 3)) (hρ : ρ ∈ Set.range compactPan) : 0 < D ρ := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hS hρ)
    obtain ⟨hnS, hgap⟩ := mem_iUnion.mp hn
    exact Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨n, hnS, hgap⟩
  have hne : (Set.range compactPan).Nonempty := by
    let μ : ProbabilityMeasure CompactTime := ⟨Measure.dirac ⟨0, by norm_num⟩, inferInstance⟩
    exact ⟨compactPan μ, ⟨μ, rfl⟩⟩
  obtain ⟨ρ, hρ, hmin⟩ := compact_pan_range_compact.exists_isMinOn hne hD.continuousOn
  exact ⟨S, D ρ, hpos ρ hρ, fun μ => hmin ⟨μ, rfl⟩⟩

end Rhone.Statistics.WeakRegularSeparation
