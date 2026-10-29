/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGToEtaReconstruction
public import Rhone.Coalescent.SmcPrimeARGFlatDensityBound
public import Rhone.Coalescent.SmcPrimeEtaExtractedDensity

/-! # The flat ARG density is dominated by the weighted reference density -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem argFlatDensity_le_etaWeightedDensity (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (p : ARGFlatCoordinate N) (hp : argFlatValid N p) :
    argFlatDensity N R p ≤
      oneProposalDensity N R (flatSkeleton N (argToEtaFlat N p)) *
        explicitEtaDensity N (argToEtaFlat N p) := by
  have hs := argFlatValid_prefix_supported N p hp
  have he := argToEtaFlat_skeleton N p hp
  rw [explicitEtaDensity_eq_extracted_exposure N (argToEtaFlat N p) (argFlatRebuild N p) hs he,
    he]
  exact argFlatDensity_le_extracted_exposure N R hR p hp

end Rhone.Coalescent.SmcPrime
