/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGToEtaCoordinates
public import Rhone.Coalescent.SmcPrimeOneSplitExtractionMeas
/-! # Joint measurability of the ARG-to-reference coordinate recoding -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory
theorem argToEtaFlat_measurable (N : ℕ) : Measurable (argToEtaFlat N) :=
  (etaSkeletonCoordinates_measurable N).comp
    ((extractOneSplitSkeleton_measurable N).comp (argFlatRebuild_measurable N))
end Rhone.Coalescent.SmcPrime
