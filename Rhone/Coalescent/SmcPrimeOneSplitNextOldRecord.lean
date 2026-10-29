/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitOldClockIntervals

/-! # Parent clades and the next old record along the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ExtractionInventory.parent_clade {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (a : Fin N)
    (i : Fin s.2.2.1) (u : Fin z.old.1.2.2.1)
    (hf : z.argLabels a = (s.2.2.2 i).1)
    (hg : z.oldLabels a = (z.old.1.2.2.2 u).1) :
    extractionClade z.oldLabels (z.old.1.2.2.2 u).1 =
      extractionClade z.argLabels (s.2.2.2 i).1 := by
  classical
  ext b
  simp only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hf, ← hg]
  exact (h.2.2.2.2 b a).symm

theorem ARGLeftInventory.rebuild_clade {N : ℕ} {s : State} {f : Fin N → ℕ}
    {d : Option ℕ} (h : ARGLeftInventory s f d) (i : Fin s.2.2.1)
    (hi : d ≠ some (s.2.2.2 i).1) :
    rebuildSampleUID f (extractionClade f (s.2.2.2 i).1) = (s.2.2.2 i).1 := by
  apply rebuildSampleUID_eq _ _ (h.clade_nonempty i hi)
  intro a ha
  exact (Finset.mem_filter.mp ha).2

theorem extractionRun_next_old_record (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (hn : n < N + 1)
    (hm : (extractionRun N h (n + 1)).mergers = (extractionRun N h n).mergers + 1) :
    (extractOneSplitSkeleton N h).1
      ⟨(extractionRun N h n).mergers + 1, by
        have hh := (extractionRun_history_prefix N h hs (n + 1) (by omega)).bound
        omega⟩ = (extractionRun N h (n + 1)).old := by
  have hb : (extractionRun N h n).mergers + 1 < N := by
    have hh := (extractionRun_history_prefix N h hs (n + 1) (by omega)).bound
    omega
  have hi : (⟨(extractionRun N h n).mergers + 1, hb⟩ : Fin N) =
      ⟨(extractionRun N h (n + 1)).mergers,
        (extractionRun_history_prefix N h hs (n + 1) (by omega)).bound⟩ := Fin.ext hm.symm
  rw [hi]
  exact extractionRun_final_old_record N h hs (n + 1) (by omega)

end Rhone.Coalescent.SmcPrime
