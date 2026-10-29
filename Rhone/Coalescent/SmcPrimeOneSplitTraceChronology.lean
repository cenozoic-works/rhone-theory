/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitTracePermutation
/-!
# Sorting the extracted trace by clocks recovers the chronological event sequence

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem extractionRebuildEventTime_injective (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    Function.Injective (rebuildEventTime (extractOneSplitSkeleton N h)) := by
  intro a b he
  obtain ⟨i, rfl⟩ := (extractionRebuildEvent_bijective N h hs).surjective a
  obtain ⟨j, rfl⟩ := (extractionRebuildEvent_bijective N h hs).surjective b
  rcases lt_trichotomy i j with hij | hij | hij
  · have ht := extractionRebuildEvent_time_strict N h hs i j hij
    rw [he] at ht
    exact False.elim (lt_irrefl _ ht)
  · subst j
    rfl
  · have ht := extractionRebuildEvent_time_strict N h hs j i hij
    rw [he] at ht
    exact False.elim (lt_irrefl _ ht)
/-- Source: marjoram_wall2006, Methods, steps 1–7. -/
theorem extractionRebuildTrace_ordered (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    (extractionRebuildTrace N h).Pairwise (fun a b =>
      rebuildEventTime (extractOneSplitSkeleton N h) a <
      rebuildEventTime (extractOneSplitSkeleton N h) b) := by
  rw [extractionRebuildTrace, ← List.ofFn_eq_map, List.pairwise_ofFn]
  intro i j hij
  exact extractionRebuildEvent_time_strict N h hs i j hij
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem rebuildEvents_extract_trace (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    rebuildEvents (extractOneSplitSkeleton N h) = extractionRebuildTrace N h := by
  classical
  let t := rebuildEventTime (extractOneSplitSkeleton N h)
  apply List.Perm.eq_of_pairwise (le := fun a b => t a ≤ t b)
  · intro a b _ _ hab hba
    exact extractionRebuildEventTime_injective N h hs (le_antisymm hab hba)
  · unfold rebuildEvents
    have hsorted := List.pairwise_mergeSort
      (le := fun a b : RebuildEvent N => decide (t a ≤ t b))
      (fun a b c hab hbc => by
        simpa only [decide_eq_true_eq] using
          (show t a ≤ t c from (of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (t a) (t b))
      ((List.finRange (N - 1)).map Sum.inl ++ [.inr false, .inr true])
    simpa only [decide_eq_true_eq] using hsorted
  · exact (extractionRebuildTrace_ordered N h hs).imp (fun hab => hab.le)
  · exact (List.mergeSort_perm _ _).trans (extractionRebuildTrace_perm N h hs).symm
end Rhone.Coalescent.SmcPrime
