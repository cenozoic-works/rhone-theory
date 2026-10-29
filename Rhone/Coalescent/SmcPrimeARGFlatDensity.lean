/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatWeight
public import Rhone.Coalescent.SmcPrimeARGWordSum

/-! # The flat density of an ARG event word agrees with the chronological event density -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem argFlatDensity_eq_weight (N : ℕ) (R : ℝ) (hR : 0 ≤ R) (p : ARGFlatCoordinate N) :
    argFlatDensity N R p = if argFlatWordOneSplit p.1 then
      if argFlatRebuild N p ∈ argPrefixFinalOne (N + 1) then argFlatWeight N R p else 0
    else 0 := by
  classical
  by_cases hw : argFlatWordOneSplit p.1
  · rw [ite_eq_left hw]
    by_cases hc : argFlatRebuild N p ∈ argPrefixFinalOne (N + 1)
    · rw [ite_eq_left hc]
      by_cases hv : argFlatValid N p
      · exact (argFlatWeight_valid N R hR p hv).symm
      · rw [show argFlatDensity N R p = 0 from ite_eq_right hv]
        symm
        by_cases hx : p.2.2 ∈ Set.Ioo 0 1
        · have he : ¬∀ j : Fin (N + 1),
              let z := argFlatRebuild N p ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩
              1 < z.1.2.2.1 ∧ argFlatActionValid z.1 (p.1 j) ∧ z.1.1 < p.2.1 j := by
            intro hh
            exact hv ⟨hw, hx, hh, hc⟩
          obtain ⟨j, hj⟩ := not_forall.mp he
          exact argFlatWeight_event_zero N R p j hj
        · exact argFlatWeight_cut_zero N R p hw hx
    · rw [ite_eq_right hc]
      apply ite_eq_right
      intro hv
      exact hc hv.2.2.2
  · rw [ite_eq_right hw]
    apply ite_eq_right
    intro hv
    exact hw hv.1

theorem argFlatWeight_measurable (N : ℕ) (R : ℝ) :
    Measurable (argFlatWeight N R) := by
  apply measurable_from_prod_countable_right
  intro w
  have hm := argWordWeight_measurable R (initialState N, (0, .inl ()))
    (argFiniteWord w) (N + 1)
  convert hm using 1
  funext p
  exact argFlatWeight_eq_word N R (w, p)

theorem argFlatDensity_measurable (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Measurable (argFlatDensity N R) := by
  have hw0 : MeasurableSet {w : Fin (N + 1) → Action | argFlatWordOneSplit w} :=
    MeasurableSet.of_discrete
  have hw : MeasurableSet {p : ARGFlatCoordinate N | argFlatWordOneSplit p.1} :=
    hw0.preimage measurable_fst
  have hc : MeasurableSet {p : ARGFlatCoordinate N |
      argFlatRebuild N p ∈ argPrefixFinalOne (N + 1)} :=
    (argPrefixFinalOne_measurable (N + 1)).preimage (argFlatRebuild_measurable N)
  have hm : Measurable (fun p : ARGFlatCoordinate N =>
      if argFlatRebuild N p ∈ argPrefixFinalOne (N + 1) then argFlatWeight N R p else 0) :=
    (argFlatWeight_measurable N R).ite hc (measurable_const (a := (0 : ℝ≥0∞)))
  have hm' : Measurable (fun p : ARGFlatCoordinate N => if argFlatWordOneSplit p.1 then
      if argFlatRebuild N p ∈ argPrefixFinalOne (N + 1) then argFlatWeight N R p else 0
    else 0) := hm.ite hw (measurable_const (a := (0 : ℝ≥0∞)))
  convert hm' using 1
  funext p
  exact argFlatDensity_eq_weight N R hR p
end Rhone.Coalescent.SmcPrime
