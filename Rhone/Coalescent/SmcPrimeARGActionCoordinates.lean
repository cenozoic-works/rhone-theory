/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcSupport.ARGActionTransitions
public import Rhone.Coalescent.SmcPrimeARGFlatRun

/-! # Flat-coordinate integrals of the pair and split action weights of the ARG recursion -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

noncomputable def argFlatPairWeight (R : ℝ) (z : AugmentedState) (ij : ℕ × ℕ)
    (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 1 < z.1.2.2.1 ∧ ij.1 < ij.2 ∧ ij.2 < z.1.2.2.1 ∧ z.1.1 < t then
    ENNReal.ofReal (Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))) else 0

noncomputable def argFlatSplitWeight (R : ℝ) (z : AugmentedState) (i : ℕ)
    (p : ℝ × ℝ) : ℝ≥0∞ := by
  classical
  exact if 1 < z.1.2.2.1 ∧ i < z.1.2.2.1 ∧ z.1.1 < p.1 ∧
      lineageHullEndpoint false z.1 i < p.2 ∧ p.2 < lineageHullEndpoint true z.1 i then
    ENNReal.ofReal (R / 2 * Real.exp (-(totalRate false R z.1 : ℝ) * (p.1 - z.1.1))) else 0

theorem argNaturalPair_flat_lintegral (R : ℝ) (z : AugmentedState) (ij : ℕ × ℕ)
    (f : AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂argNaturalTransition R z (.inl ij)) =
      ∫⁻ t, argFlatPairWeight R z ij t * f (argFlatActionStep z (.inl ij) t 0) := by
  classical
  by_cases hv : 1 < z.1.2.2.1 ∧ ij.1 < ij.2 ∧ ij.2 < z.1.2.2.1
  · have hi := hv.2.1.trans hv.2.2
    rw [argNaturalTransition_pair_valid R z hv.1 ⟨ij.1, hi⟩ ⟨ij.2, hv.2.2⟩ hv.2.1,
      argPairTransition_lintegral R z _ _ f hf, ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : z.1.1 < t
    · simp [argFlatPairWeight, hv.1, hv.2.1, hv.2.2, ht, argFlatActionStep,
        coalSuccessorNat, hi]
    · simp [argFlatPairWeight, ht]
  · rw [argNaturalTransition_pair_invalid R z ij hv, lintegral_zero_measure]
    have hw (t : ℝ) : argFlatPairWeight R z ij t = 0 := by
      apply ite_eq_right
      tauto
    simp only [hw, zero_mul, lintegral_zero]

theorem argNaturalSplit_flat_lintegral (R : ℝ) (z : AugmentedState) (i : ℕ)
    (f : AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂argNaturalTransition R z (.inr i)) =
      ∫⁻ p : ℝ × ℝ, argFlatSplitWeight R z i p *
        f (argFlatActionStep z (.inr i) p.1 p.2) := by
  classical
  by_cases hv : 1 < z.1.2.2.1 ∧ i < z.1.2.2.1
  · rw [argNaturalTransition_split_valid R z hv.1 ⟨i, hv.2⟩,
      argSplitTransition_lintegral R z _ f hf, Measure.prod_restrict,
      ← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
    apply lintegral_congr
    intro p
    by_cases hp : z.1.1 < p.1 ∧
        hullLo (z.1.2.2.2 ⟨i, hv.2⟩).2 < p.2 ∧ p.2 < hullHi (z.1.2.2.2 ⟨i, hv.2⟩).2
    · simp [argFlatSplitWeight, lineageHullEndpoint,
        hv.1, hv.2, hp.1, hp.2.1, hp.2.2, argFlatActionStep, splitSuccessorNat]
    · have hnot : p ∉ Set.Ioi z.1.1 ×ˢ Set.Ioo (hullLo (z.1.2.2.2 ⟨i, hv.2⟩).2)
          (hullHi (z.1.2.2.2 ⟨i, hv.2⟩).2) := hp
      simp only [Set.indicator_of_notMem hnot, argFlatSplitWeight, lineageHullEndpoint,
        dite_eq_left hv.2, Bool.false_eq_true, ite_false, ite_true]
      rw [ite_eq_right (by tauto), zero_mul]
  · rw [argNaturalTransition_split_invalid R z i hv, lintegral_zero_measure]
    have hw (p : ℝ × ℝ) : argFlatSplitWeight R z i p = 0 := by
      apply ite_eq_right
      tauto
    simp only [hw, zero_mul, lintegral_zero]
end Rhone.Coalescent.SmcPrime
