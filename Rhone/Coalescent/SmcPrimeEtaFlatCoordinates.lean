/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanFlatLaw
public import Rhone.Coalescent.SmcPrimeReferenceFlatMeas
public import Rhone.Probability.ProbabilityDensityTransport

/-!
# Coordinates and explicit density of the one-split reference measure

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory Set
open Probability.MeasureTransport
open scoped ENNReal

abbrev EtaFlatMark (N : ℕ) := (Fin (N - 1) → ℕ × ℕ) × ℕ × Finset (Fin N)

abbrev EtaFlatCoordinate (N : ℕ) := EtaFlatMark N × MarkedClocks (N + 1)

def etaOldTimes (N : ℕ) (τ : Fin (N + 1) → ℝ) : Fin (N - 1) → ℝ :=
  fun j => τ ⟨j.val, by have := j.isLt; omega⟩

def etaCutTime (N : ℕ) (τ : Fin (N + 1) → ℝ) : ℝ := τ ⟨N - 1, by omega⟩

def etaAttachmentTime (N : ℕ) (τ : Fin (N + 1) → ℝ) : ℝ := τ ⟨N, by omega⟩

noncomputable def flatSkeleton (N : ℕ) (p : EtaFlatCoordinate N) : OneSplitSkeleton N :=
  (oldPairHistory N p.1.1 (etaOldTimes N p.2.1), p.1.2.1,
    etaCutTime N p.2.1, p.2.2, etaAttachmentTime N p.2.1, p.1.2.2)

noncomputable def explicitEtaDensity (N : ℕ) (p : EtaFlatCoordinate N) : ℝ≥0∞ := by
  classical
  let h := oldPairHistory N p.1.1 (etaOldTimes N p.2.1)
  let T := metricTreeFromHistory N h
  let t := etaCutTime N p.2.1
  let U := etaAttachmentTime N p.2.1
  exact oldPairDensity N p.1.1 (etaOldTimes N p.2.1) * indexedCutDensity T (p.1.2.1, t) *
    if p.2.2 ∈ Ioo 0 1 ∧ t ≤ U then
      ENNReal.ofReal (Real.exp (-attachmentHazard T t U) * attachmentTargetRate T U p.1.2.2)
    else 0

theorem etaOldTimes_measurable (N : ℕ) : Measurable (etaOldTimes N) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem flatSkeleton_measurable (N : ℕ) : Measurable (flatSkeleton N) := by
  have hh : Measurable (fun p : EtaFlatCoordinate N =>
      oldPairHistory N p.1.1 (etaOldTimes N p.2.1)) :=
    (oldPairHistory_measurable N).comp (measurable_fst.fst.prodMk
      ((etaOldTimes_measurable N).comp measurable_snd.fst))
  exact hh.prodMk (measurable_fst.snd.fst.prodMk
    (((measurable_pi_apply (⟨N - 1, by omega⟩ : Fin (N + 1))).comp measurable_snd.fst).prodMk
      (measurable_snd.snd.prodMk
        (((measurable_pi_apply (⟨N, by omega⟩ : Fin (N + 1))).comp measurable_snd.fst).prodMk
          measurable_fst.snd.snd))))

theorem explicitEtaDensity_measurable (N : ℕ) : Measurable (explicitEtaDensity N) := by
  classical
  apply measurable_from_prod_countable_right
  intro a
  let P := MarkedClocks (N + 1)
  have hh : Measurable (fun p : P => oldPairHistory N a.1 (etaOldTimes N p.1)) :=
    (oldPairHistory_measurable N).comp
      (measurable_const.prodMk ((etaOldTimes_measurable N).comp measurable_fst))
  have hT := (metricTreeFromHistory_measurable N).comp hh
  have ht : Measurable (fun p : P => etaCutTime N p.1) :=
    (measurable_pi_apply (⟨N - 1, by omega⟩ : Fin (N + 1))).comp measurable_fst
  have hU : Measurable (fun p : P => etaAttachmentTime N p.1) :=
    (measurable_pi_apply (⟨N, by omega⟩ : Fin (N + 1))).comp measurable_fst
  have ho : Measurable (fun p : P => oldPairDensity N a.1 (etaOldTimes N p.1)) :=
    (oldPairDensity_measurable N).comp
      (measurable_const.prodMk ((etaOldTimes_measurable N).comp measurable_fst))
  have hc := (indexedCutDensity_joint_measurable N).comp
    (hT.prodMk ((measurable_const (a := a.2.1)).prodMk ht))
  have ha := (attachmentHazard_joint_measurable N).comp (hT.prodMk (ht.prodMk hU))
  have hr := (attachmentTargetRate_joint_measurable N a.2.2).comp (hT.prodMk hU)
  exact (ho.mul hc).mul (((ha.neg.exp.mul hr).ennreal_ofReal).ite
    (((measurableSet_Ioo.preimage measurable_snd)).inter (measurableSet_le ht hU))
    measurable_const)

end Rhone.Coalescent.SmcPrime
