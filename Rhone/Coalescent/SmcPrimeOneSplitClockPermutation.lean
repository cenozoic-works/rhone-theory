/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitTraceChronology

/-! # Extracted old merger, cut, and attachment clocks are a permutation of the event clocks -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractOneSplitSkeleton_clock_perm (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    ((List.finRange (N + 1)).map (fun k =>
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1)).Perm
      (((List.finRange (N - 1)).map (fun k =>
        ((extractOneSplitSkeleton N h).1 ⟨k.val + 1,
          by have := k.isLt; omega⟩).1.1)) ++
        [(extractOneSplitSkeleton N h).2.2.1,
          (extractOneSplitSkeleton N h).2.2.2.2.1]) := by
  have hp := (extractionRebuildTrace_perm N h hs).map
    (rebuildEventTime (extractOneSplitSkeleton N h))
  simp only [extractionRebuildTrace, List.map_map, List.map_append, List.map_cons,
    List.map_nil, Function.comp_def, rebuildEventTime] at hp
  convert hp using 1
  apply List.map_congr_left
  intro k _
  exact (extractionRebuildEvent_time N h hs k).symm

end Rhone.Coalescent.SmcPrime
