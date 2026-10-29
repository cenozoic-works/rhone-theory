/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeEtaFlatCoordinates
public import Rhone.Coalescent.SmcPrimeARGFlatPrefixSupport
public import Rhone.Coalescent.SmcPrimeOneSplitRebuildInverse
/-! # Recoding of flat ARG coordinates into one-split reference coordinates -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
open Probability.MeasureTransport
def etaHistoryPairWord (N : ℕ) (h : KingmanHistory N) (j : Fin (N - 1)) : ℕ × ℕ :=
  let c := genealogyEventCode (h ⟨j.val + 1, by have := j.isLt; omega⟩).2.2
  (c.2.1,c.2.2.1)
noncomputable def etaSkeletonCoordinates (N : ℕ) (η : OneSplitSkeleton N) :
    EtaFlatCoordinate N :=
  ((etaHistoryPairWord N η.1,η.2.1,η.2.2.2.2.2),
    ((fun j => if hj : j.val < N - 1 then
      (η.1 ⟨j.val + 1, by omega⟩).1.1
      else if j.val = N - 1 then η.2.2.1 else η.2.2.2.2.1),η.2.2.2.1))
noncomputable def argToEtaFlat (N : ℕ) (p : ARGFlatCoordinate N) : EtaFlatCoordinate N :=
  etaSkeletonCoordinates N (extractOneSplitSkeleton N (argFlatRebuild N p))
theorem etaHistoryPairWord_measurable (N : ℕ) : Measurable (etaHistoryPairWord N) := by
  apply measurable_pi_iff.mpr
  intro j
  have he : Measurable (fun h : KingmanHistory N =>
      (h ⟨j.val + 1, by have := j.isLt; omega⟩).2.2) :=
    (measurable_pi_apply _).snd.snd
  have hc := genealogyEventCode_measurable.comp he
  exact hc.snd.fst.prodMk hc.snd.snd.fst
theorem etaSkeletonCoordinates_measurable (N : ℕ) : Measurable (etaSkeletonCoordinates N) := by
  have ht : Measurable (fun η : OneSplitSkeleton N => fun j : Fin (N + 1) =>
      if hj : j.val < N - 1 then (η.1 ⟨j.val + 1, by omega⟩).1.1
      else if j.val = N - 1 then η.2.2.1 else η.2.2.2.2.1) := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j.val < N - 1
    · simp only [dite_eq_left hj]
      exact ((measurable_pi_apply _).comp measurable_fst).fst.fst
    · simp only [dite_eq_right hj]
      by_cases he : j.val = N - 1
      · simp only [ite_eq_left he]; exact measurable_snd.snd.fst
      · simp only [ite_eq_right he]; exact measurable_snd.snd.snd.snd.fst
  exact (((etaHistoryPairWord_measurable N).comp measurable_fst).prodMk
    (measurable_snd.fst.prodMk measurable_snd.snd.snd.snd.snd)).prodMk
      (ht.prodMk measurable_snd.snd.snd.fst)
end Rhone.Coalescent.SmcPrime
