/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGZeroSectorLaw
public import Rhone.Coalescent.SmcPrimeSectorDensityLaw

/-!
# The full ARG genealogy law at zero recombination is the Kingman tree law

Source: hudson1983, eq. (13), p. 197; griffiths1991_two_locus_graph, p. 103; kingman1982, sec. 1,
eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport

theorem treeConstantGenealogy_measurable (N : ℕ) :
    Measurable (fun T : Tree N => (fun _ i j => treePairMRCA T i j : Genealogy N)) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    treePairMRCA_measurable N i j

theorem eventProcess_zero_noSplit (N : ℕ) :
    ∀ᵐ ω ∂(eventProcess false 0).pathLaw (initialState N, (0, .inl ())),
      ω ∈ argNoSplitPathSet := by
  filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
    eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hc hk
  intro k
  cases k with
  | zero => simp [hc.1, argNoSplitEvent, genealogyEventCode]
  | succ k => exact (hk k).noSplit

/-- Source: hudson1983, eq. (13), p. 197; griffiths1991_two_locus_graph, p. 103. -/
theorem fullARGGenealogyLaw_zero_eq_kingmanTree (N : ℕ) :
    fullARGGenealogyLaw N 0 =
      (kingmanTreeLaw N).map (fun T => fun _ i j => treePairMRCA T i j) := by
  have hfull : fullARGGenealogyLaw N 0 = zeroSplitARGGenealogySector N 0 := by
    unfold zeroSplitARGGenealogySector fullARGGenealogyLaw
    rw [Measure.restrict_eq_self_of_ae_mem (eventProcess_zero_noSplit N)]
  have hd : (fun h : KingmanHistory N => ENNReal.ofReal
      (Real.exp (-((0 : ℝ) / 2 * treeLength (metricTreeFromHistory N h))))) = 1 := by
    funext h
    simp
  rw [hfull, zeroSplitARGGenealogySector_eq N 0 le_rfl,
    zeroProposalGenealogySector_density N 0 le_rfl, hd, withDensity_one, kingmanTreeLaw,
    Measure.map_map (treeConstantGenealogy_measurable N) (metricTreeFromHistory_measurable N)]
  rfl

end Rhone.Coalescent.SmcPrime
