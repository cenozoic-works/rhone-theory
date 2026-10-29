/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeOldPairReconstruction
public import Rhone.Coalescent.SmcPrimeARGFlatInjective
/-! # The ARG-to-reference recoding is injective and recovers the extracted skeleton -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess
theorem etaSkeletonCoordinates_skeleton (N : ℕ) (hN : 0 < N) (η : OneSplitSkeleton N)
    (hs : KingmanHistorySupported N η.1)
    (hc : ∀ k, (η.1 k).2.1 = (η.1 k).1.1) :
    flatSkeleton N (etaSkeletonCoordinates N η) = η := by
  have ho : etaOldTimes N (etaSkeletonCoordinates N η).2.1 =
      fun j => (η.1 ⟨j.val+1,by have := j.isLt; omega⟩).1.1 := by
    funext j
    simp only [etaOldTimes, etaSkeletonCoordinates, dite_eq_left j.isLt]
  have ht : etaCutTime N (etaSkeletonCoordinates N η).2.1 = η.2.2.1 := by
    simp [etaCutTime, etaSkeletonCoordinates]
  have hU : etaAttachmentTime N (etaSkeletonCoordinates N η).2.1 = η.2.2.2.2.1 := by
    have hn : ¬ N < N - 1 := by omega
    have hne : N ≠ N - 1 := by omega
    simp only [etaAttachmentTime, etaSkeletonCoordinates, dite_eq_right hn,
      ite_eq_right hne]
  change (oldPairHistory N (etaHistoryPairWord N η.1)
      (etaOldTimes N (etaSkeletonCoordinates N η).2.1),η.2.1,
      etaCutTime N (etaSkeletonCoordinates N η).2.1,η.2.2.2.1,
      etaAttachmentTime N (etaSkeletonCoordinates N η).2.1,η.2.2.2.2.2) = η
  rw [ho,oldPairHistory_decoded N hN η.1 hs hc,ht,hU]
theorem argFlatValid_pos (N : ℕ) (p : ARGFlatCoordinate N) (hp : argFlatValid N p) : 0 < N := by
  have hn := (hp.2.2.1 ⟨0,by omega⟩).1
  change 1 < N at hn
  omega
theorem argToEtaFlat_skeleton (N : ℕ) (p : ARGFlatCoordinate N) (hp : argFlatValid N p) :
    flatSkeleton N (argToEtaFlat N p) =
      extractOneSplitSkeleton N (argFlatRebuild N p) := by
  apply etaSkeletonCoordinates_skeleton N (argFlatValid_pos N p hp)
  · exact extractOneSplitSkeleton_history_supported N (argFlatRebuild N p)
      (argFlatValid_prefix_supported N p hp)
  · exact extractOneSplitSkeleton_history_clock N (argFlatRebuild N p)
theorem argToEtaFlat_injOn (N : ℕ) :
    Set.InjOn (argToEtaFlat N) {p | argFlatValid N p} := by
  intro p hp q hq he
  apply argFlatRebuild_injOn N hp hq
  apply extractOneSplitSkeleton_injOn N
    (argFlatValid_prefix_supported N p hp) (argFlatValid_prefix_supported N q hq)
  rw [← argToEtaFlat_skeleton N p hp,← argToEtaFlat_skeleton N q hq,he]
end Rhone.Coalescent.SmcPrime
