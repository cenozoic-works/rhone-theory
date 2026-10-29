/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeLimit

/-!
# Joint infinitesimal limit of trait values along a pedigree

Source: barton_etheridge_veber2017, sec. 3.1. -/

@[expose] public section
namespace Rhone.Unproved
open MeasureTheory ProbabilityTheory Filter Topology Rhone.Combinatorics Statistics
open scoped BoundedContinuousFunction

/-- Source: barton_etheridge_veber2017, sec. 3.1. -/
theorem infinitesimal_pedigree_tendsto_gaussian {n : ℕ} (P : Pedigree n) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (g : (Fin n → ℝ) →ᵇ ℝ) :
    Tendsto (fun M : ℕ => ∫ ω, g (segregationResidual P (traitDeviation P (∫ y, y ∂ν) M ω))
        ∂(genomeLaw n ν M))
      atTop (𝓝 (∫ z, g z ∂(Measure.pi fun i =>
        gaussianReal 0 (segregationVariance P (variance id ν) i).toNNReal))) := by
  exact Rhone.Statistics.infinitesimal_pedigree_tendsto_gaussian P ν hν g

end Rhone.Unproved
