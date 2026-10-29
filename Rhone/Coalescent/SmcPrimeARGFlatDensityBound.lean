/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitARGDensityBound
public import Rhone.Coalescent.SmcPrimeARGFlatPrefixSupport
public import Rhone.Coalescent.SmcPrimeARGFlatSupport

/-! # The flat ARG density is bounded by the exponential of the extracted exposure -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem argFlatDensity_le_extracted_exposure (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (p : ARGFlatCoordinate N) (hp : argFlatValid N p) :
    let η := extractOneSplitSkeleton N (argFlatRebuild N p)
    argFlatDensity N R p ≤ oneProposalDensity N R η *
      ENNReal.ofReal (Real.exp (-oldCoalExposure N η.1 -
        attachmentHazard (metricTreeFromHistory N η.1) η.2.2.1 η.2.2.2.2.1)) := by
  dsimp only
  have hs := argFlatValid_prefix_supported N p hp
  have hc (k : Fin (N + 1)) := argFlatRebuild_clock N p k
  have he := oneSplitARGDensity_le_proposal N R hR (argFlatRebuild N p) hs
  dsimp only at he
  simp only [hc] at he
  unfold argFlatDensity
  rw [ite_eq_left hp]
  exact he

end Rhone.Coalescent.SmcPrime
