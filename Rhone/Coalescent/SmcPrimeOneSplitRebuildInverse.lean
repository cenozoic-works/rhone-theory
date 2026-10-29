/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuildFold
public import Rhone.Coalescent.SmcPrimeOneSplitTraceChronology

/-! # Rebuilding inverts the extraction, which is injective on its image -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

theorem oneSplitRebuild_extract (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (k : Fin (N + 2)) :
    oneSplitRebuild N (extractOneSplitSkeleton N h) k =
      h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩ := by
  unfold oneSplitRebuild
  rw [rebuildEvents_extract_trace N h hs]
  exact (extractionRebuildFold_eq_prefix N h hs k.val (by omega)).1

theorem extractOneSplitSkeleton_injOn (N : ℕ) :
    Set.InjOn (extractOneSplitSkeleton N) {h | OneSplitPrefixSupported N h} := by
  intro h hh g hg he
  funext k
  have hk : k.val < N + 2 := by
    have := Finset.mem_Iic.mp k.property
    omega
  have ha := oneSplitRebuild_extract N h hh ⟨k.val, hk⟩
  have hb := oneSplitRebuild_extract N g hg ⟨k.val, hk⟩
  rw [he] at ha
  exact ha.symm.trans hb

theorem oneSplitARGPrefixLaw_rebuild_extract (N : ℕ) (R : ℝ) :
    ∀ᵐ h ∂oneSplitARGPrefixLaw N R, ∀ k : Fin (N + 2),
      oneSplitRebuild N (extractOneSplitSkeleton N h) k =
        h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩ := by
  filter_upwards [oneSplitARGPrefixLaw_supported N R] with h hs
  exact oneSplitRebuild_extract N h hs

end Rhone.Coalescent.SmcPrime
