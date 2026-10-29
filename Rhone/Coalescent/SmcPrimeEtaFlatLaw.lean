/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeEtaProductRegroup
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative
public import Rhone.Coalescent.SmcPrimeKingmanChronology

/-!
# Flat law of the one-split reference measure in counting-mark and clock coordinates

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess
open scoped ENNReal

noncomputable def etaFiberBase (N : ℕ) : Measure (EtaFiberCoordinate N) :=
  ((Measure.count : Measure ℕ).prod volume).prod
    (volume.prod (volume.prod (Measure.count : Measure (Finset (Fin N)))))

noncomputable def etaOldBase (N : ℕ) :
    Measure ((Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ)) :=
  (Measure.count : Measure (Fin (N - 1) → ℕ × ℕ)).prod volume

instance etaFiberBase_sfinite (N : ℕ) : SFinite (etaFiberBase N) := by
  unfold etaFiberBase
  infer_instance

instance etaOldBase_sfinite (N : ℕ) : SFinite (etaOldBase N) := by
  unfold etaOldBase
  infer_instance

noncomputable def etaRawMap (N : ℕ) (p : EtaRawCoordinate N) : OneSplitSkeleton N :=
  etaFiberMap N (oldPairHistory N p.1.1 p.1.2) p.2

noncomputable def etaRawDensity (N : ℕ) (p : EtaRawCoordinate N) : ℝ≥0∞ :=
  oldPairDensity N p.1.1 p.1.2 *
    etaFiberDensity (metricTreeFromHistory N (oldPairHistory N p.1.1 p.1.2)) p.2

theorem etaRawMap_measurable (N : ℕ) : Measurable (etaRawMap N) := by
  have hh : Measurable (fun p : EtaRawCoordinate N => oldPairHistory N p.1.1 p.1.2) :=
    (oldPairHistory_measurable N).comp measurable_fst
  exact hh.prodMk (measurable_snd.fst.fst.prodMk
    (measurable_snd.fst.snd.prodMk (measurable_snd.snd.fst.prodMk
      (measurable_snd.snd.snd.fst.prodMk measurable_snd.snd.snd.snd))))

theorem etaRawDensity_measurable (N : ℕ) : Measurable (etaRawDensity N) := by
  have hh : Measurable (fun p : EtaRawCoordinate N => oldPairHistory N p.1.1 p.1.2) :=
    (oldPairHistory_measurable N).comp measurable_fst
  exact ((oldPairDensity_measurable N).comp measurable_fst).mul
    ((etaFiberDensity_joint_measurable N).comp
      (((metricTreeFromHistory_measurable N).comp hh).prodMk measurable_snd))

theorem oneSplitReferenceMeasure_raw_flat (N : ℕ) (hN : 0 < N) :
    oneSplitReferenceMeasure N =
      (((etaOldBase N).prod (etaFiberBase N)).withDensity (etaRawDensity N)).map
        (etaRawMap N) := by
  let ν := etaFiberBase N
  apply Measure.ext_of_lintegral
  intro f hf
  let ψ (h : KingmanHistory N) :=
    ∫⁻ p, etaFiberDensity (metricTreeFromHistory N h) p * f (etaFiberMap N h p) ∂ν
  have hm : Measurable (fun p : KingmanHistory N × EtaFiberCoordinate N =>
      etaFiberDensity (metricTreeFromHistory N p.1) p.2 * f (etaFiberMap N p.1 p.2)) := by
    exact ((etaFiberDensity_joint_measurable N).comp
      (((metricTreeFromHistory_measurable N).comp measurable_fst).prodMk measurable_snd)).mul
        (hf.comp (by unfold etaFiberMap; fun_prop))
  have hψ : Measurable ψ := hm.lintegral_prod_right'
  have ho : Measurable (fun p : EtaRawCoordinate N => f (etaRawMap N p)) :=
    hf.comp (etaRawMap_measurable N)
  rw [lintegral_map hf (etaRawMap_measurable N),
    lintegral_withDensity_eq_lintegral_mul _ (etaRawDensity_measurable N) ho,
    lintegral_prod _ ((etaRawDensity_measurable N).mul ho).aemeasurable,
    oneSplitReferenceMeasure, Measure.lintegral_bind
      (oneSplitReferenceFiber_measurable N).aemeasurable hf.aemeasurable]
  calc
    (∫⁻ h, ∫⁻ s, f s ∂oneSplitReferenceFiber N h ∂kingmanHistoryLaw N) =
        ∫⁻ h, ψ h ∂kingmanHistoryLaw N := by
      apply lintegral_congr_ae
      filter_upwards [kingmanHistoryLaw_tree_nonnegative N,
        kingmanHistoryLaw_tree_chronology N hN] with h hn hc
      rw [oneSplitReferenceFiber_flat N h hn (tree_chronology_temporal_cover _ hN hc),
        lintegral_map hf (etaFiberMap_measurable N h)]
      exact lintegral_withDensity_eq_lintegral_mul _ (etaFiberDensity_measurable _)
        (show Measurable (fun p => f (etaFiberMap N h p)) from
          hf.comp (etaFiberMap_measurable N h))
    _ = ∫⁻ p, oldPairDensity N p.1 p.2 * ψ (oldPairHistory N p.1 p.2) ∂etaOldBase N := by
      rw [kingmanHistoryLaw_pair_flat N hN, lintegral_map hψ (oldPairHistory_measurable N)]
      have hp : Measurable (fun p : (Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ) =>
          ψ (oldPairHistory N p.1 p.2)) := hψ.comp (oldPairHistory_measurable N)
      rw [lintegral_withDensity_eq_lintegral_mul _ (oldPairDensity_measurable N) hp]
      rfl
    _ = _ := by
      apply lintegral_congr
      intro p
      have hp : oldPairDensity N p.1 p.2 ≠ ⊤ := by
        unfold oldPairDensity
        exact argWordWeight_ne_top _ _ _ _ _ _
      rw [← lintegral_const_mul' _ _ hp]
      apply lintegral_congr
      intro q
      simp only [etaRawDensity, etaRawMap, Pi.mul_apply, mul_assoc]

end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Probability.MeasureTransport
open scoped ENNReal

theorem etaRawMap_unpack (n : ℕ) (p : EtaFlatCoordinate (n + 1)) :
    etaRawMap (n + 1) (etaCoordinateUnpack n p) = flatSkeleton (n + 1) p := by
  rw [etaCoordinateUnpack_apply]
  rfl

theorem etaRawDensity_unpack (n : ℕ) (p : EtaFlatCoordinate (n + 1)) :
    etaRawDensity (n + 1) (etaCoordinateUnpack n p) = explicitEtaDensity (n + 1) p := by
  rw [etaCoordinateUnpack_apply]
  simp only [etaRawDensity, etaFiberDensity, explicitEtaDensity, mul_assoc]

theorem oneSplitReferenceMeasure_flat (N : ℕ) (hN : 0 < N) :
    oneSplitReferenceMeasure N =
      (((Measure.count : Measure (EtaFlatMark N)).prod volume).withDensity
        (explicitEtaDensity N)).map (flatSkeleton N) := by
  cases N with
  | zero => omega
  | succ n =>
    rw [oneSplitReferenceMeasure_raw_flat (n + 1) hN]
    apply Measure.ext_of_lintegral
    intro f hf
    have ho : Measurable (fun p : EtaRawCoordinate (n + 1) => f (etaRawMap (n + 1) p)) :=
      hf.comp (etaRawMap_measurable (n + 1))
    have ht : Measurable (fun p : EtaFlatCoordinate (n + 1) => f (flatSkeleton (n + 1) p)) :=
      hf.comp (flatSkeleton_measurable (n + 1))
    rw [lintegral_map hf (etaRawMap_measurable (n + 1)),
      lintegral_map hf (flatSkeleton_measurable (n + 1)),
      lintegral_withDensity_eq_lintegral_mul _ (etaRawDensity_measurable (n + 1)) ho,
      lintegral_withDensity_eq_lintegral_mul _ (explicitEtaDensity_measurable (n + 1)) ht]
    simp only [etaOldBase, etaFiberBase]
    rw [(etaCoordinateUnpack_preserving n).lintegral_map_equiv
      (f := etaRawDensity (n + 1) * fun p => f (etaRawMap (n + 1) p))]
    apply lintegral_congr
    intro p
    simp only [Pi.mul_apply, etaRawDensity_unpack, etaRawMap_unpack]

end Rhone.Coalescent.SmcPrime
