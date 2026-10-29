/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuildEvent

/-! # Folding the extracted event trace chronologically reproduces the ARG prefix -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

noncomputable def extractionRebuildFold (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : ℕ) : RebuildState N :=
  ((extractionRebuildTrace N h).take n).foldl
    (rebuildStep (extractOneSplitSkeleton N h)) (rebuildInitial N)

theorem extractionRebuildFold_succ (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : ℕ) (hn : n < N + 1) :
    extractionRebuildFold N h (n + 1) =
      rebuildStep (extractOneSplitSkeleton N h) (extractionRebuildFold N h n)
        (extractionRebuildEvent N (extractionRun N h n)
          (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩)
          (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩)) := by
  unfold extractionRebuildFold
  have hlen : n < (extractionRebuildTrace N h).length := by
    simpa only [extractionRebuildTrace, List.length_map, List.length_finRange] using hn
  rw [List.take_succ_eq_append_getElem hlen, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [extractionRebuildTrace, List.getElem_map, List.getElem_finRange]
  rfl

theorem extractionRebuildFold_eq_prefix (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n ≤ N + 1) :
    (extractionRebuildFold N h n).1 = h ⟨n, Finset.mem_Iic.mpr hn⟩ ∧
      (extractionRebuildFold N h n).2.1 = (extractionRun N h n).argLabels ∧
      (extractionRebuildFold N h n).2.2.2 = (extractionRun N h n).detached := by
  induction n with
  | zero =>
    rw [hs.1]
    exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    have hlt : n < N + 1 := by omega
    have hh := ih (by omega)
    have heq : extractionRebuildFold N h n =
        (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩, (extractionRun N h n).argLabels,
          (extractionRebuildFold N h n).2.2.1, (extractionRun N h n).detached) :=
      Prod.ext hh.1 (Prod.ext hh.2.1 (Prod.ext rfl hh.2.2))
    rw [extractionRebuildFold_succ N h n hlt, heq]
    exact rebuildStep_extractionRebuildEvent N h hs ⟨n, hlt⟩
      (extractionRebuildFold N h n).2.2.1

end Rhone.Coalescent.SmcPrime
