/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeObservedFlatDensity
public import Rhone.Coalescent.SmcPrimeARGFlatPrefixSupport
public import Rhone.Coalescent.SmcPrimeSectorDensityLaw
public import Rhone.Coalescent.SmcPrimeARGOneSectorLaw
public import Rhone.Coalescent.SmcPrimeARGFlatSupport

/-! # Genuine observed one-proposal and one-split sectors retain their derived flat densities -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

theorem oneSplitARGGenealogySector_flat (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    oneSplitARGGenealogySector N R =
      ((((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).restrict
        {p : ARGFlatCoordinate N | argFlatValid N p}).withDensity (argFlatDensity N R)).map
          (fun p => oneSkeletonGenealogy N (extractOneSplitSkeleton N (argFlatRebuild N p))) := by
  rw [oneSplitARGGenealogySector, oneSplitARGPrefixLaw_flat N R hR,
    argFlatDensity_restrict_valid N R,
    Measure.map_map (argPrefixGenealogy_measurable N) (argFlatRebuild_measurable N)]
  apply Measure.map_congr
  have hv : ∀ᵐ p ∂((((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).restrict
      {p : ARGFlatCoordinate N | argFlatValid N p}).withDensity (argFlatDensity N R)),
      argFlatValid N p :=
    (ae_withDensity_iff (argFlatDensity_measurable N R hR)).mpr
      ((ae_restrict_mem (argFlatValid_measurable N)).mono (fun _ hp _ => hp))
  filter_upwards [hv] with p hp
  exact (extractOneSplitSkeleton_genealogy N (argFlatRebuild N p)
    (argFlatValid_prefix_supported N p hp)).symm

end Rhone.Coalescent.SmcPrime
