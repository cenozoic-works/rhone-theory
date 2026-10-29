/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeEtaFlatLaw
public import Rhone.Coalescent.SmcPrimeSectorDensityLaw
public import Rhone.Coalescent.SmcPrimeARGOneSectorLaw
public import Rhone.Coalescent.SmcPrimeARGFlatSupport

/-! # Genuine observed one-proposal and one-split sectors retain their derived flat densities -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

theorem oneProposalGenealogySector_flat (N : ℕ) (hN : 0 < N) (R : ℝ) (hR : 0 ≤ R) :
    oneProposalGenealogySector N R =
      (((Measure.count : Measure (EtaFlatMark N)).prod volume).withDensity
        (fun p => oneProposalDensity N R (flatSkeleton N p) * explicitEtaDensity N p)).map
          (fun p => oneSkeletonGenealogy N (flatSkeleton N p)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have ho : Measurable (fun p => oneSkeletonGenealogy N (flatSkeleton N p)) :=
    (oneSkeletonGenealogy_measurable N).comp (flatSkeleton_measurable N)
  have hb : Measurable (fun p => oneProposalDensity N R (flatSkeleton N p)) :=
    (oneProposalDensity_measurable N R).comp (flatSkeleton_measurable N)
  have hg : Measurable (fun η => f (oneSkeletonGenealogy N η)) :=
    hf.comp (oneSkeletonGenealogy_measurable N)
  rw [oneProposalGenealogySector_density N R hR,
    lintegral_map hf (oneSkeletonGenealogy_measurable N),
    lintegral_withDensity_eq_lintegral_mul _ (oneProposalDensity_measurable N R) hg,
    oneSplitReferenceMeasure_flat N hN,
    lintegral_map ((oneProposalDensity_measurable N R).mul hg)
      (flatSkeleton_measurable N)]
  simp only [Pi.mul_apply]
  have hl : Measurable (fun p => oneProposalDensity N R (flatSkeleton N p) *
      f (oneSkeletonGenealogy N (flatSkeleton N p))) := hb.mul (hf.comp ho)
  have hw : Measurable (fun p => oneProposalDensity N R (flatSkeleton N p) *
      explicitEtaDensity N p) := hb.mul (explicitEtaDensity_measurable N)
  have hof : Measurable (fun p => f (oneSkeletonGenealogy N (flatSkeleton N p))) := hf.comp ho
  rw [lintegral_withDensity_eq_lintegral_mul _ (explicitEtaDensity_measurable N) hl,
    lintegral_map hf ho, lintegral_withDensity_eq_lintegral_mul _ hw hof]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply]
  ac_rfl

theorem argFlatDensity_restrict_valid (N : ℕ) (R : ℝ) :
    ((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).withDensity
        (argFlatDensity N R) =
      (((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).restrict
        {p : ARGFlatCoordinate N | argFlatValid N p}).withDensity (argFlatDensity N R) := by
  rw [← withDensity_indicator (argFlatValid_measurable N)]
  congr 1
  funext p
  by_cases hp : argFlatValid N p <;> simp [Set.indicator, hp, argFlatDensity]

end Rhone.Coalescent.SmcPrime
