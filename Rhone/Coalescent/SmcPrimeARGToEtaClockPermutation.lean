/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeARGToEtaReconstruction
public import Rhone.Coalescent.SmcPrimeOneSplitClockPermutation
public import Rhone.Coalescent.SmcPrimeOneSplitARGWitness
public import Rhone.Probability.ProbabilityPermutationTransport
/-! # The clock coordinates of the ARG-to-reference recoding form a permutation -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
open Probability.MeasureTransport

def etaClockTag (N : ℕ) (j : Fin (N + 1)) : RebuildEvent N :=
  if hj : j.val < N - 1 then .inl ⟨j.val, hj⟩
  else if j.val = N - 1 then .inr false else .inr true

theorem etaClockTag_bijective (N : ℕ) (hN : 0 < N) :
    Function.Bijective (etaClockTag N) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j he
    apply Fin.ext
    by_cases hi : i.val < N - 1 <;> by_cases hj : j.val < N - 1
    · simp only [etaClockTag, dite_eq_left hi, dite_eq_left hj] at he
      exact congrArg (fun k : Fin (N - 1) => k.val) (Sum.inl.inj he)
    · simp only [etaClockTag, dite_eq_left hi, dite_eq_right hj] at he
      split_ifs at he
    · simp only [etaClockTag, dite_eq_right hi, dite_eq_left hj] at he
      split_ifs at he
    · by_cases hi0 : i.val = N - 1 <;> by_cases hj0 : j.val = N - 1
      · omega
      · simp [etaClockTag, hj, hi0, hj0] at he
      · simp [etaClockTag, hi, hi0, hj0] at he
      · have := i.isLt; have := j.isLt; omega
  · simp only [RebuildEvent, Fintype.card_fin, Fintype.card_sum, Fintype.card_bool]
    omega

theorem etaSkeletonCoordinates_clock (N : ℕ) (η : OneSplitSkeleton N)
    (j : Fin (N + 1)) :
    (etaSkeletonCoordinates N η).2.1 j = rebuildEventTime η (etaClockTag N j) := by
  by_cases hj : j.val < N - 1
  · simp [etaSkeletonCoordinates, etaClockTag, hj, rebuildEventTime]
  · by_cases he : j.val = N - 1 <;>
      simp [etaSkeletonCoordinates, etaClockTag, hj, he, rebuildEventTime]

theorem argToEtaFlat_clockPermutation (N : ℕ) (p : ARGFlatCoordinate N)
    (hp : argFlatValid N p) :
    ∃ σ : Equiv.Perm (Fin (N + 1)),
      (argToEtaFlat N p).2 = clockPermutation σ p.2 := by
  classical
  let h := argFlatRebuild N p
  let η := extractOneSplitSkeleton N h
  have hs := argFlatValid_prefix_supported N p hp
  let E : Fin (N + 1) ≃ RebuildEvent N := Equiv.ofBijective
    (fun k => extractionRebuildEvent N (extractionRun N h k.val)
      (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩))
    (extractionRebuildEvent_bijective N h hs)
  let G : Fin (N + 1) ≃ RebuildEvent N :=
    Equiv.ofBijective (etaClockTag N) (etaClockTag_bijective N (argFlatValid_pos N p hp))
  let σ : Equiv.Perm (Fin (N + 1)) := E.trans G.symm
  have ht (k : Fin (N + 1)) : rebuildEventTime η (E k) = p.2.1 k :=
    (extractionRebuildEvent_time N h hs k).trans (argFlatRebuild_clock N p k)
  have hx : η.2.2.2.1 = p.2.2 := by
    obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
    have hc := (extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
      w.cutPosition w.cut_event w.other_event).2
    have hev := argFlatRebuild_event N p w.cutStep
    have hw : (h ⟨w.cutStep.val + 1, Finset.mem_Iic.mpr w.cutStep.isLt⟩).2.2 =
        .inr (.inr (w.cutIndex, w.cutPosition)) := by
      simpa only [extractionPrefixExtension_prefix N h (w.cutStep.val + 1)
        w.cutStep.isLt] using w.cut_event
    rw [hw] at hev
    have he : w.cutPosition = p.2.2 := by
      cases ha : p.1 w.cutStep with
      | inl ij => simp only [ha] at hev; cases hev
      | inr i =>
        simp only [ha] at hev
        exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj hev))
    exact hc.trans he
  refine ⟨σ, Prod.ext ?_ ?_⟩
  · funext i
    have hr : ((clockPermutation σ) p.2).1 i = p.2.1 (σ.symm i) := by
      change (MeasurableEquiv.piCongrLeft (fun _ : Fin (N + 1) => ℝ) σ) p.2.1 i = _
      simpa only [σ.apply_symm_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ : Fin (N + 1) => ℝ)
          p.2.1 (σ.symm i))
    rw [hr]
    change (etaSkeletonCoordinates N η).2.1 i = p.2.1 (σ.symm i)
    rw [etaSkeletonCoordinates_clock]
    have he : E (σ.symm i) = etaClockTag N i := E.apply_symm_apply (G i)
    rw [← he, ht]
  · exact hx
end Rhone.Coalescent.SmcPrime
