/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeExtractionStepMeas
/-! # Measurability of the one-split extraction fold and run -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
theorem extractionFold_measurable (N : ℕ) (l : List (Fin (N + 1))) :
    Measurable (fun p : OneSplitExtractionState N × ARGPrefix (N + 1) =>
      l.foldl (fun z k => extractionStep z
        (p.2 ⟨k.val,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
        (p.2 ⟨k.val+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) p.1) := by
  induction l with
  | nil => exact measurable_fst
  | cons k l ih =>
    have hp : Measurable (fun p : OneSplitExtractionState N × ARGPrefix (N+1) =>
        p.2 ⟨k.val,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩) :=
      (measurable_pi_apply _).comp measurable_snd
    have hn : Measurable (fun p : OneSplitExtractionState N × ARGPrefix (N+1) =>
        p.2 ⟨k.val+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩) :=
      (measurable_pi_apply _).comp measurable_snd
    have hs := (extractionStep_measurable N).comp (measurable_fst.prodMk (hp.prodMk hn))
    simpa only [List.foldl_cons,Function.comp_def] using ih.comp (hs.prodMk measurable_snd)
theorem extractionRun_measurable (N n : ℕ) : Measurable (fun h => extractionRun N h n) := by
  exact (extractionFold_measurable N ((List.finRange (N+1)).take n)).comp
    (measurable_const.prodMk measurable_id)
theorem extractOneSplitSkeleton_measurable (N : ℕ) : Measurable (extractOneSplitSkeleton N) := by
  have hz := extractionRun_measurable N (N+1)
  have hh := (extractionOldHistory_measurable N).comp hz
  have hc := (extractionCut_measurable N).comp hz
  have ha := (extractionAttachment_measurable N).comp hz
  have hidx := (extractionCutIndex_measurable N).comp
    (((metricTreeFromHistory_measurable N).comp hh).prodMk (hc.fst.prodMk hc.snd.fst))
  exact hh.prodMk (hidx.prodMk (hc.snd.fst.prodMk (hc.snd.snd.prodMk
    (ha.fst.prodMk ha.snd))))
end Rhone.Coalescent.SmcPrime
