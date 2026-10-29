/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitCoalExposure
public import Rhone.Coalescent.SmcPrimeOneSplitHullExposure

/-! # The one-split ARG density is dominated by the extracted proposal factors -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oneSplitARGDensity_le_proposal (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (h : ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h) :
    let η := extractOneSplitSkeleton N h
    let s := fun k : Fin (N + 1) => (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1
    let δ := fun k : Fin (N + 1) =>
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1 - (s k).1
    ENNReal.ofReal (R / 2 * Real.exp
      (-argCoalExposure s δ - R / 2 * argHullExposure s δ)) ≤
      oneProposalDensity N R η *
        ENNReal.ofReal (Real.exp (-oldCoalExposure N η.1 -
          attachmentHazard (metricTreeFromHistory N η.1) η.2.2.1 η.2.2.2.2.1)) := by
  dsimp only
  rw [oneSplitCoalExposure_eq N h hs]
  unfold oneProposalDensity
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have he := extractOneSplitSkeleton_hull_exposure N h hs
  dsimp only at he
  have he' :
      (extractOneSplitSkeleton N h).2.2.2.1 *
          treeLength (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) +
        (1 - (extractOneSplitSkeleton N h).2.2.2.1) *
          treeLength (oneSplitPostTree (extractOneSplitSkeleton N h)) ≤
      argHullExposure
        (fun k : Fin (N + 1) => (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1)
        (fun k => (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).1.1 -
          (h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) := by
    have hp (k : Fin (N + 1)) :=
      extractionPrefixExtension_prefix N h k.val k.isLt.le
    have hn (k : Fin (N + 1)) :=
      extractionPrefixExtension_prefix N h (k.val + 1) k.isLt
    simpa only [hp, hn] using he
  have hm := mul_le_mul_of_nonneg_left he' (show 0 ≤ R / 2 by positivity)
  linarith

end Rhone.Coalescent.SmcPrime
