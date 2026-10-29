/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGPrefixObservation

/-! # The one-split sector of the ARG genealogy law -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

def argOnePrefixPathSet (N : ℕ) : Set EventPath :=
  {ω | (fun k : Finset.Iic (N + 1) => ω k.val) ∈ oneSplitPrefixSector N}

theorem argOnePrefixPathSet_measurable (N : ℕ) : MeasurableSet (argOnePrefixPathSet N) :=
  (oneSplitPrefixSector_measurable N).preimage
    (measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val))

noncomputable def oneSplitARGGenealogySector (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  (oneSplitARGPrefixLaw N R).map (argPrefixGenealogy N)

theorem oneSplitARGGenealogySector_eq_restrict (N : ℕ) (R : ℝ) :
    oneSplitARGGenealogySector N R =
      (((eventProcess false R).pathLaw (initialState N, (0, .inl ()))).restrict
        (argOnePrefixPathSet N)).map (genealogyObservation N) := by
  let F (ω : EventPath) : ARGPrefix (N + 1) := fun k => ω k.val
  have hF : Measurable F := measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
  rw [oneSplitARGGenealogySector, oneSplitARGPrefixLaw, argPrefixLaw,
    Measure.restrict_map hF (oneSplitPrefixSector_measurable N),
    Measure.map_map (argPrefixGenealogy_measurable N) hF]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (argOnePrefixPathSet_measurable N),
    ae_restrict_of_ae (eventProcess_chronologicalAncestryPath N false R)] with ω hp hc
  change argPrefixGenealogy N (fun k : Finset.Iic (N + 1) => ω k.val) = genealogyObservation N ω
  rw [argPrefixGenealogy_prefix]
  exact (genealogy_eq_prefix_of_one N ω hc (N + 1) hp.2).symm

theorem oneSplitARGGenealogySector_skeleton (N : ℕ) (R : ℝ) :
    oneSplitARGGenealogySector N R = (oneSplitARGPrefixLaw N R).map
      (fun h => oneSkeletonGenealogy N (extractOneSplitSkeleton N h)) := by
  apply Measure.map_congr
  filter_upwards [oneSplitARGPrefixLaw_supported N R] with h hs
  exact (extractOneSplitSkeleton_genealogy N h hs).symm

theorem arg_zero_one_path_disjoint (N : ℕ) :
    Disjoint argNoSplitPathSet (argOnePrefixPathSet N) := by
  apply Set.disjoint_left.mpr
  intro ω hz ho
  obtain ⟨⟨c, hc, _⟩, _⟩ := ho
  exact (arg_noSplit_event_iff _).mp (hz (c.val + 1)) hc

end Rhone.Coalescent.SmcPrime
