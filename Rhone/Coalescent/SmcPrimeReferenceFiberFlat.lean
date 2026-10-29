/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeReferenceFlatMeas
public import Rhone.Coalescent.SmcPrimeReferenceSkeleton

/-!
# Flat law of the fibres of the one-split reference measure

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory Set
open scoped ENNReal

theorem attachmentGenomicLaw_flat {N : ℕ} (T : Tree N) (hT : TreeTemporalCover T)
    (t : ℝ) (ht : 0 ≤ t) :
    (volume.restrict (Ioo (0 : ℝ) 1)).prod (attachmentUniformLaw T t) =
      (volume.prod (volume.prod (Measure.count : Measure (Finset (Fin N))))).withDensity
        (fun p => if p.1 ∈ Ioo 0 1 ∧ t ≤ p.2.1 then
          ENNReal.ofReal (Real.exp (-attachmentHazard T t p.2.1) *
            attachmentTargetRate T p.2.1 p.2.2) else 0) := by
  classical
  let d : ℝ × Finset (Fin N) → ℝ≥0∞ := fun p => if t ≤ p.1 then
    ENNReal.ofReal (Real.exp (-attachmentHazard T t p.1) *
      attachmentTargetRate T p.1 p.2) else 0
  have hd : Measurable d := by
    apply measurable_from_prod_countable_left
    intro c
    exact (((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable.mul
      (measurable_attachmentTargetRate T c)).ennreal_ofReal).piecewise
        measurableSet_Ici measurable_const
  rw [attachmentUniformLaw_flat T hT t ht]
  change (volume.restrict (Ioo (0 : ℝ) 1)).prod
    ((volume.prod Measure.count).withDensity d) = _
  rw [← withDensity_indicator_one measurableSet_Ioo]
  have hx : Measurable ((Ioo (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Ioo
  rw [prod_withDensity hx hd]
  congr 1
  funext p
  by_cases hx : p.1 ∈ Ioo 0 1 <;> by_cases ht : t ≤ p.2.1 <;>
    simp [d, hx, ht, Set.indicator]

theorem indexedCutDensity_nonnegative_time {N : ℕ} (T : Tree N)
    (hT : TreeNonnegative T) (p : ℕ × ℝ) (hp : indexedCutDensity T p ≠ 0) :
    0 ≤ p.2 := by
  classical
  unfold indexedCutDensity at hp
  split_ifs at hp with hb hs
  · exact (hT ⟨p.1, hb⟩).trans hs.2.2.1.le
  · exact False.elim (hp rfl)
  · exact False.elim (hp rfl)

end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory ProbabilityTheory Set
open scoped ENNReal

abbrev EtaFiberCoordinate (N : ℕ) := (ℕ × ℝ) × (ℝ × (ℝ × Finset (Fin N)))

def etaFiberMap (N : ℕ) (h : KingmanHistory N) (p : EtaFiberCoordinate N) :
    OneSplitSkeleton N := (h, p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2)

noncomputable def etaFiberDensity {N : ℕ} (T : Tree N) (p : EtaFiberCoordinate N) : ℝ≥0∞ := by
  classical
  exact indexedCutDensity T p.1 * if p.2.1 ∈ Ioo 0 1 ∧ p.1.2 ≤ p.2.2.1 then
    ENNReal.ofReal (Real.exp (-attachmentHazard T p.1.2 p.2.2.1) *
      attachmentTargetRate T p.2.2.1 p.2.2.2) else 0

theorem etaFiberMap_measurable (N : ℕ) (h : KingmanHistory N) :
    Measurable (etaFiberMap N h) := by unfold etaFiberMap; fun_prop

theorem etaFiberDensity_measurable {N : ℕ} (T : Tree N) :
    Measurable (etaFiberDensity T) := by
  classical
  have hc : Measurable (fun p : EtaFiberCoordinate N => indexedCutDensity T p.1) :=
    (indexedCutDensity_measurable T).comp measurable_fst
  have hh : Measurable (fun p : EtaFiberCoordinate N =>
      attachmentHazard T p.1.2 p.2.2.1) :=
    (attachmentHazard_joint_measurable N).comp
      (measurable_const.prodMk (measurable_fst.snd.prodMk measurable_snd.snd.fst))
  have hr : Measurable (fun p : EtaFiberCoordinate N =>
      attachmentTargetRate T p.2.2.1 p.2.2.2) := by
    apply measurable_countable_choice (fun p : EtaFiberCoordinate N => p.2.2.2)
      measurable_snd.snd.snd (fun c p => attachmentTargetRate T p.2.2.1 c)
    intro c
    exact (measurable_attachmentTargetRate T c).comp measurable_snd.snd.fst
  exact hc.mul (((hh.neg.exp.mul hr).ennreal_ofReal).ite
    ((measurableSet_Ioo.preimage measurable_snd.fst).inter
      (measurableSet_le measurable_fst.snd measurable_snd.snd.fst)) measurable_const)

theorem etaFiberDensity_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × EtaFiberCoordinate N => etaFiberDensity p.1 p.2) := by
  classical
  let P := Tree N × EtaFiberCoordinate N
  have hc : Measurable (fun p : P => indexedCutDensity p.1 p.2.1) :=
    (indexedCutDensity_joint_measurable N).comp (measurable_fst.prodMk measurable_snd.fst)
  have hh : Measurable (fun p : P => attachmentHazard p.1 p.2.1.2 p.2.2.2.1) :=
    (attachmentHazard_joint_measurable N).comp
      (measurable_fst.prodMk (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd.fst))
  have hr : Measurable (fun p : P => attachmentTargetRate p.1 p.2.2.2.1 p.2.2.2.2) := by
    apply measurable_countable_choice (fun p : P => p.2.2.2.2) measurable_snd.snd.snd.snd
      (fun c p => attachmentTargetRate p.1 p.2.2.2.1 c)
    intro c
    exact (attachmentTargetRate_joint_measurable N c).comp
      (measurable_fst.prodMk measurable_snd.snd.snd.fst)
  exact hc.mul (((hh.neg.exp.mul hr).ennreal_ofReal).ite
    ((measurableSet_Ioo.preimage measurable_snd.snd.fst).inter
      (measurableSet_le measurable_snd.fst.snd measurable_snd.snd.snd.fst)) measurable_const)

theorem oneSplitReferenceFiber_flat (N : ℕ) (h : KingmanHistory N)
    (hn : TreeNonnegative (metricTreeFromHistory N h))
    (hc : TreeTemporalCover (metricTreeFromHistory N h)) :
    oneSplitReferenceFiber N h =
      ((((Measure.count : Measure ℕ).prod volume).prod
        (volume.prod (volume.prod (Measure.count : Measure (Finset (Fin N)))))).withDensity
          (etaFiberDensity (metricTreeFromHistory N h))).map (etaFiberMap N h) := by
  let T := metricTreeFromHistory N h
  have hk : Measurable (fun bt : ℕ × ℝ => oneSplitTailKernel N (h, bt)) :=
    (oneSplitTailKernel N).measurable.comp (measurable_const.prodMk measurable_id)
  have he : oneSplitReferenceFiber N h =
      (indexedTreeCutMeasure T).bind (fun bt => oneSplitTailKernel N (h, bt)) := by
    simp only [oneSplitReferenceFiber, oneSplitTailKernel_apply, T]
  apply Measure.ext_of_lintegral
  intro f hf
  have ho : Measurable (fun p : EtaFiberCoordinate N => f (etaFiberMap N h p)) :=
    hf.comp (etaFiberMap_measurable N h)
  have hi : Measurable (fun bt : ℕ × ℝ =>
      ∫⁻ z, f z ∂oneSplitTailKernel N (h, bt)) :=
    (Measure.measurable_lintegral hf).comp hk
  rw [lintegral_map hf (etaFiberMap_measurable N h),
    lintegral_withDensity_eq_lintegral_mul _ (etaFiberDensity_measurable T) ho,
    lintegral_prod _ ((etaFiberDensity_measurable T).mul ho).aemeasurable,
    he, Measure.lintegral_bind hk.aemeasurable hf.aemeasurable, indexedTreeCutMeasure_flat,
    lintegral_withDensity_eq_lintegral_mul _ (indexedCutDensity_measurable T)
      hi]
  apply lintegral_congr
  intro bt
  simp only [Pi.mul_apply]
  by_cases hd : indexedCutDensity T bt = 0
  · simp [etaFiberDensity, hd]
  · have ht := indexedCutDensity_nonnegative_time T hn bt hd
    rw [oneSplitTailKernel_apply, lintegral_map hf (by fun_prop),
      attachmentGenomicLaw_flat T hc bt.2 ht]
    have hs : Measurable (fun xa : ℝ × (ℝ × Finset (Fin N)) =>
        f (h, bt.1, bt.2, xa.1, xa.2.1, xa.2.2)) := hf.comp (by fun_prop)
    have htail : Measurable (fun xa : ℝ × (ℝ × Finset (Fin N)) =>
        if xa.1 ∈ Ioo 0 1 ∧ bt.2 ≤ xa.2.1 then
          ENNReal.ofReal (Real.exp (-attachmentHazard T bt.2 xa.2.1) *
            attachmentTargetRate T xa.2.1 xa.2.2) else 0) := by
      have hh : Measurable (fun xa : ℝ × (ℝ × Finset (Fin N)) =>
          attachmentHazard T bt.2 xa.2.1) :=
        (continuous_attachmentHazard T bt.2).measurable.comp measurable_snd.fst
      have hr : Measurable (fun xa : ℝ × (ℝ × Finset (Fin N)) =>
          attachmentTargetRate T xa.2.1 xa.2.2) := by
        apply measurable_countable_choice (fun xa : ℝ × (ℝ × Finset (Fin N)) => xa.2.2)
          measurable_snd.snd (fun c xa => attachmentTargetRate T xa.2.1 c)
        intro c
        exact (measurable_attachmentTargetRate T c).comp measurable_snd.fst
      exact ((hh.neg.exp.mul hr).ennreal_ofReal).ite
        ((measurableSet_Ioo.preimage measurable_fst).inter
          (measurableSet_le measurable_const measurable_snd.fst)) measurable_const
    rw [lintegral_withDensity_eq_lintegral_mul _ htail hs]
    have hfinite : indexedCutDensity T bt ≠ ⊤ := by
      unfold indexedCutDensity
      split_ifs <;> simp
    rw [← lintegral_const_mul' _ _ hfinite]
    apply lintegral_congr
    intro xa
    simp only [etaFiberDensity, etaFiberMap, Pi.mul_apply, mul_assoc]

end Rhone.Coalescent.SmcPrime
