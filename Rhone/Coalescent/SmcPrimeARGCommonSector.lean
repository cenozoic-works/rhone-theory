/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGOneSectorLaw

/-! # Common-sector mass and the unrestricted ARG second-split bound -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport SmcBound
open MeasureTheory

noncomputable def fewSplitARGGenealogySector (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  zeroSplitARGGenealogySector N R + oneSplitARGGenealogySector N R

theorem fewSplitARGGenealogySector_eq_restrict (N : ℕ) (hN : 0 < N) (R : ℝ) :
    fewSplitARGGenealogySector N R =
      (((eventProcess false R).pathLaw (initialState N, (0, .inl ()))).restrict
        eventTwoSplitsᶜ).map (genealogyObservation N) := by
  have hp : argNoSplitPathSet ∪ argOnePrefixPathSet N =ᵐ[
      (eventProcess false R).pathLaw (initialState N, (0, .inl ()))] eventTwoSplitsᶜ := by
    filter_upwards [eventProcess_chronologicalAncestryPath N false R,
      eventProcess_ARGTransition R (initialState N, (0, .inl ()))] with ω hc ht
    apply propext
    exact (arg_path_sector_partition N hN ω hc.1 ht).symm
  rw [fewSplitARGGenealogySector, zeroSplitARGGenealogySector,
    oneSplitARGGenealogySector_eq_restrict,
    ← Measure.map_add _ _ (genealogyObservation_measurable N),
    ← Measure.restrict_union (arg_zero_one_path_disjoint N) (argOnePrefixPathSet_measurable N),
    Measure.restrict_congr_set hp]

theorem fewSplitARGGenealogySector_le (N : ℕ) (hN : 0 < N) (R : ℝ) :
    fewSplitARGGenealogySector N R ≤ fullARGGenealogyLaw N R := by
  rw [fewSplitARGGenealogySector_eq_restrict N hN R, fullARGGenealogyLaw]
  exact Measure.map_mono Measure.restrict_le_self (genealogyObservation_measurable N)

theorem fewSplitARGGenealogySector_mass_defect (N : ℕ) (hN : 0 < N) (R : ℝ) (hR : 0 ≤ R) :
    1 - (fewSplitARGGenealogySector N R).real Set.univ ≤ doubleBound R (N - 1) := by
  let μ := (eventProcess false R).pathLaw (initialState N, (0, .inl ()))
  have hmass : (fewSplitARGGenealogySector N R).real Set.univ = μ.real eventTwoSplitsᶜ := by
    rw [fewSplitARGGenealogySector_eq_restrict N hN R]
    simp only [Measure.real, Measure.map_apply (genealogyObservation_measurable N)
      MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    rfl
  have hsum := measureReal_add_measureReal_compl (μ := μ) eventTwoSplits_measurable
  rw [probReal_univ] at hsum
  have hbound : μ.real eventTwoSplits ≤ doubleBound R (N - 1) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ eventTwoSplits)
      (doubleBound_nonneg R hR (N - 1))).mp (event_two_splits_le false R hR N hN)
  rw [hmass]
  linarith

end Rhone.Coalescent.SmcPrime
