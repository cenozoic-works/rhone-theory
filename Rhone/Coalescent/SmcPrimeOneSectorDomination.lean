/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGObservedFlatDensity
public import Rhone.Coalescent.SmcPrimeARGToEtaMeas
public import Rhone.Coalescent.SmcPrimeARGToEtaClockPermutation
public import Rhone.Coalescent.SmcPrimePointwiseDensityComparison
public import Rhone.Probability.ProbabilityDensityTransport

/-! # The one-split ARG sector is dominated by the one-proposal sector -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open Probability.MeasureTransport
open scoped ENNReal

theorem oneSplitARGGenealogySector_le_oneProposal (N : ℕ) (hN : 0 < N)
    (R : ℝ) (hR : 0 ≤ R) :
    oneSplitARGGenealogySector N R ≤ oneProposalGenealogySector N R := by
  let A : Set (ARGFlatCoordinate N) := {p | argFlatValid N p}
  let μ : Measure (ARGFlatCoordinate N) :=
    (((Measure.count : Measure (Fin (N + 1) → Action)).prod volume).restrict A).withDensity
      (argFlatDensity N R)
  let g : EtaFlatCoordinate N → ℝ≥0∞ := fun p =>
    oneProposalDensity N R (flatSkeleton N p) * explicitEtaDensity N p
  let G : EtaFlatCoordinate N → Genealogy N := fun p =>
    oneSkeletonGenealogy N (flatSkeleton N p)
  have hg : Measurable g :=
    ((oneProposalDensity_measurable N R).comp (flatSkeleton_measurable N)).mul
      (explicitEtaDensity_measurable N)
  have hG : Measurable G :=
    (oneSkeletonGenealogy_measurable N).comp (flatSkeleton_measurable N)
  have ht := markedPermutation_density_le (N + 1) A (argFlatValid_measurable N)
    (argToEtaFlat N) (argToEtaFlat_measurable N) (argToEtaFlat_injOn N)
    (fun p hp => (argFlatValid_clocks_strictMono N p hp).injective)
    (fun p hp => argToEtaFlat_clockPermutation N p hp)
    (argFlatDensity N R) g hg
    (fun p hp => argFlatDensity_le_etaWeightedDensity N R hR p hp)
  have ho := Measure.map_mono ht hG
  rw [Measure.map_map hG (argToEtaFlat_measurable N)] at ho
  have hv : ∀ᵐ p ∂μ, argFlatValid N p :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (argFlatValid_measurable N))
  rw [oneSplitARGGenealogySector_flat N R hR, oneProposalGenealogySector_flat N hN R hR]
  change μ.map (fun p => oneSkeletonGenealogy N
      (extractOneSplitSkeleton N (argFlatRebuild N p))) ≤
    (((Measure.count : Measure (EtaFlatMark N)).prod volume).withDensity g).map G
  calc
    _ = μ.map (G ∘ argToEtaFlat N) := Measure.map_congr (by
      filter_upwards [hv] with p hp
      dsimp only [G, Function.comp_def]
      rw [argToEtaFlat_skeleton N p hp])
    _ ≤ _ := ho

end Rhone.Coalescent.SmcPrime
