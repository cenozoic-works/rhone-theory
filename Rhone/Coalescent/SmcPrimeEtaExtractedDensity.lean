/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeEtaFlatCoordinates
public import Rhone.Coalescent.SmcPrimeOldPairExponential
public import Rhone.Coalescent.SmcPrimeExtractedDensitySupport

/-! # The explicit one-split reference density equals the extracted exposure form -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem explicitEtaDensity_eq_extracted_exposure (N : ℕ) (p : EtaFlatCoordinate N)
    (h : ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (he : flatSkeleton N p = extractOneSplitSkeleton N h) :
    explicitEtaDensity N p = ENNReal.ofReal (Real.exp
      (-oldCoalExposure N (extractOneSplitSkeleton N h).1 -
        attachmentHazard (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
          (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1)) := by
  classical
  let η := flatSkeleton N p
  have hold : KingmanHistorySupported N (oldPairHistory N p.1.1 (etaOldTimes N p.2.1)) := by
    change KingmanHistorySupported N η.1
    dsimp only [η]
    rw [he]
    exact extractOneSplitSkeleton_history_supported N h hs
  unfold explicitEtaDensity
  rw [oldPairDensity_eq_exposure N p.1.1 (etaOldTimes N p.2.1) hold]
  change ENNReal.ofReal (Real.exp (-oldCoalExposure N η.1)) *
    indexedCutDensity (metricTreeFromHistory N η.1) (η.2.1, η.2.2.1) *
      (if η.2.2.2.1 ∈ Set.Ioo 0 1 ∧ η.2.2.1 ≤ η.2.2.2.2.1 then
        ENNReal.ofReal (Real.exp
          (-attachmentHazard (metricTreeFromHistory N η.1) η.2.2.1 η.2.2.2.2.1) *
          attachmentTargetRate (metricTreeFromHistory N η.1) η.2.2.2.2.1 η.2.2.2.2.2)
      else 0) = _
  dsimp only [η]
  simp only [he]
  rw [extractOneSplitSkeleton_indexedCutDensity N h hs,
    extractOneSplitSkeleton_attachmentTargetRate N h hs, mul_one, mul_one]
  have hx : (extractOneSplitSkeleton N h).2.2.2.1 ∈ Set.Ioo 0 1 := by
    obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
    rw [(extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
      w.cutPosition w.cut_event w.other_event).2]
    exact ⟨w.cut_pos, w.cut_lt_one⟩
  have ht := (extractOneSplitSkeleton_cut_geometry N h hs).2.1
  rw [ite_eq_left ⟨hx, ht⟩, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2

end Rhone.Coalescent.SmcPrime
