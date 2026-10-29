/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CompactBivariateMoments
public import Rhone.Statistics.Identifiability.FiniteSiteObservationLaw
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Uniqueness of nonnegative bivariate Laplace transforms by time compactification -/

@[expose] public section

noncomputable section
open MeasureTheory

namespace Rhone.Statistics.Identifiability

def compactifyTime (t : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-max t 0), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _))⟩

def compactifyTimes (t : ℝ × ℝ) : CompactMomentSquare :=
  (compactifyTime t.1, compactifyTime t.2)

theorem measurable_compactifyTimes : Measurable compactifyTimes := by
  have hc : Continuous compactifyTimes := by
    unfold compactifyTimes compactifyTime
    fun_prop
  exact hc.measurable

def uncompactifyTimes (x : CompactMomentSquare) : ℝ × ℝ :=
  (-Real.log x.1.val, -Real.log x.2.val)

theorem measurable_uncompactifyTimes : Measurable uncompactifyTimes := by
  unfold uncompactifyTimes
  fun_prop

theorem recover_compactifyTimes {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) :
    uncompactifyTimes (compactifyTimes t) = t := by
  simp [uncompactifyTimes, compactifyTimes, compactifyTime,
    max_eq_left ht.1, max_eq_left ht.2]

theorem recover_map_compactifyTimes (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) :
    (μ.map compactifyTimes).map uncompactifyTimes = μ := by
  rw [Measure.map_map measurable_uncompactifyTimes measurable_compactifyTimes]
  calc
    μ.map (uncompactifyTimes ∘ compactifyTimes) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with t ht
      exact recover_compactifyTimes ht
    _ = μ := Measure.map_id

theorem compactified_mixed_moment (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) (m n : ℕ) :
    (∫ x : CompactMomentSquare, x.1.val ^ m * x.2.val ^ n ∂μ.map compactifyTimes) =
      ∫ t, Real.exp (-(m : ℝ) * t.1) * Real.exp (-(n : ℝ) * t.2) ∂μ := by
  rw [integral_map measurable_compactifyTimes.aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x : CompactMomentSquare => x.1.val ^ m * x.2.val ^ n)
      (μ.map compactifyTimes))]
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  simp only [compactifyTimes, compactifyTime, max_eq_left ht.1, max_eq_left ht.2]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 2 <;> ring

theorem nonnegative_bivariate_laplace_unique
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    (hlap : ∀ m n : ℕ,
      (∫ t, Real.exp (-(m : ℝ) * t.1) * Real.exp (-(n : ℝ) * t.2) ∂μ) =
        ∫ t, Real.exp (-(m : ℝ) * t.1) * Real.exp (-(n : ℝ) * t.2) ∂ν) :
    μ = ν := by
  have hmap : μ.map compactifyTimes = ν.map compactifyTimes := by
    apply compact_bivariate_moment_unique
    intro m n
    rw [compactified_mixed_moment μ hμ m n, compactified_mixed_moment ν hν m n]
    exact hlap m n
  calc
    μ = (μ.map compactifyTimes).map uncompactifyTimes := (recover_map_compactifyTimes μ hμ).symm
    _ = (ν.map compactifyTimes).map uncompactifyTimes :=
      congrArg (Measure.map uncompactifyTimes) hmap
    _ = ν := recover_map_compactifyTimes ν hν

end Rhone.Statistics.Identifiability
