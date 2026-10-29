/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatDensity

/-! # Flat-coordinate law of the one-split ARG prefix sector -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem oneSplitARGPrefixLaw_flat (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    oneSplitARGPrefixLaw N R =
      (((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).withDensity
        (argFlatDensity N R)).map (argFlatRebuild N) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hfo : Measurable (fun p : ARGFlatCoordinate N => f (argFlatRebuild N p)) :=
    hf.comp (argFlatRebuild_measurable N)
  have hg : Measurable (fun p : ARGFlatCoordinate N =>
      argFlatDensity N R p * f (argFlatRebuild N p)) :=
    (argFlatDensity_measurable N R hR).mul hfo
  rw [lintegral_map hf (argFlatRebuild_measurable N),
    lintegral_withDensity_eq_lintegral_mul _ (argFlatDensity_measurable N R hR)
      hfo]
  change (∫⁻ h, f h ∂oneSplitARGPrefixLaw N R) =
    ∫⁻ p : ARGFlatCoordinate N, argFlatDensity N R p * f (argFlatRebuild N p)
      ∂(Measure.count.prod volume)
  rw [lintegral_prod _ hg.aemeasurable, lintegral_count,
    argOneSector_lintegral_sum N R f hf]
  apply tsum_congr
  intro w
  by_cases hw : argFlatWordOneSplit w
  · rw [ite_eq_left hw, argOneWord_flat_lintegral R hR _ (argFiniteWord w) (N + 1)
      ((argWordOneSplit_finite w).mpr hw)
      ((argPrefixFinalOne (N + 1)).indicator f)
      (hf.indicator (argPrefixFinalOne_measurable (N + 1)))]
    apply lintegral_congr
    intro p
    rw [← argFlatRebuild_eq_word N (w, p), ← argFlatWeight_eq_word N R (w, p),
      argFlatDensity_eq_weight N R hR (w, p), ite_eq_left hw]
    by_cases hc : argFlatRebuild N (w, p) ∈ argPrefixFinalOne (N + 1)
    · rw [Set.indicator_of_mem hc, ite_eq_left hc]
    · rw [Set.indicator_of_notMem hc, ite_eq_right hc, mul_zero, zero_mul]
  · rw [ite_eq_right hw]
    symm
    calc
      _ = ∫⁻ _p : (Fin (N + 1) → ℝ) × ℝ, (0 : ℝ≥0∞) := lintegral_congr fun p => by
        rw [argFlatDensity_eq_weight N R hR (w, p), ite_eq_right hw, zero_mul]
      _ = 0 := lintegral_zero
end Rhone.Coalescent.SmcPrime
