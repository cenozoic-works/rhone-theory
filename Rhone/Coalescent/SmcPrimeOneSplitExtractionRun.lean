/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction

/-! # Left ancestor labels and partition updates during one-split extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_argLabels {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) :
    (extractionStep z pre next).argLabels =
      fun i => ancestorStep pre.1 next.2.2 leftBoundaryProbe (z.argLabels i) := by
  classical
  unfold extractionStep
  split <;> simp only
  split <;> rfl

theorem extractionRun_succ (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : ℕ) (hn : n < N + 1) :
    extractionRun N h (n + 1) = extractionStep (extractionRun N h n)
      (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩)
      (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩) := by
  unfold extractionRun
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using hn),
    List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_finRange]
  rfl

def extractionPrefixExtension (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) : EventPath :=
  fun k => if hk : k ≤ N + 1 then h ⟨k, Finset.mem_Iic.mpr hk⟩
    else (initialState N, (0, .inl ()))

theorem extractionPrefixExtension_prefix (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (k : ℕ) (hk : k ≤ N + 1) :
    extractionPrefixExtension N h k = h ⟨k, Finset.mem_Iic.mpr hk⟩ := by
  simp only [extractionPrefixExtension, dite_eq_left hk]

theorem extractionRun_argLabels (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : ℕ) (hn : n ≤ N + 1)
    (i : Fin N) :
    (extractionRun N h n).argLabels i =
      ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [extractionRun_succ N h n (by omega), extractionStep_argLabels]
    simp only [ancestorLabel, extractionPrefixExtension_prefix N h n (by omega),
      extractionPrefixExtension_prefix N h (n + 1) hn, ih (by omega)]

end Rhone.Coalescent.SmcPrime
