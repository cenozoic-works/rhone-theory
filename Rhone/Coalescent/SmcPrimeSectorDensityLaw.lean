/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeZeroSectorLaw
public import Rhone.Coalescent.SmcPrimeOneSectorLaw
public import Rhone.Coalescent.SmcPrimeProposalSectorDensity
/-!
# Densities of the zero- and one-proposal genealogy sectors

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem zeroProposalGenealogySector_density (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    zeroProposalGenealogySector N R =
      ((kingmanHistoryLaw N).withDensity (fun h => ENNReal.ofReal
        (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h)))))).map
          (zeroHistoryGenealogy N) := by
  rw [← zeroProposalHistorySource_density N R hR, zeroProposalHistorySource_genealogy]

theorem oneProposalGenealogySector_density (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    oneProposalGenealogySector N R =
      ((oneSplitReferenceMeasure N).withDensity (oneProposalDensity N R)).map
        (oneSkeletonGenealogy N) := by
  rw [← oneProposalSkeletonSource_density N R hR, oneProposalSkeletonSource_genealogy]
end Rhone.Coalescent.SmcPrime
