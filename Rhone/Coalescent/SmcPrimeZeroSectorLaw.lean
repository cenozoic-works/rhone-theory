/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeSourcePath
public import Rhone.Coalescent.SmcPrimeProposalSectorDensity
/-!
# The zero-proposal history source induces the zero-proposal observed sector

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

noncomputable def zeroHistoryGenealogy (N : ℕ) (h : KingmanHistory N) : Genealogy N :=
  fun _ i j => treePairMRCA (metricTreeFromHistory N h) i j

theorem zeroHistoryGenealogy_measurable (N : ℕ) : Measurable (zeroHistoryGenealogy N) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact (treePairMRCA_measurable N i j).comp (metricTreeFromHistory_measurable N)

theorem history_first_mark_law (N : ℕ) :
    ((kingmanHistoryLaw N).prod sourceProposalStreamLaw).map
      (fun p => (p.1, p.2 0)) = (kingmanHistoryLaw N).prod proposalNoiseLaw := by
  simpa only [Measure.map_id, source_first_mark_law, Prod.map_def, id_eq] using
    (Measure.map_prod_map (kingmanHistoryLaw N) sourceProposalStreamLaw measurable_id
      (measurable_pi_apply 0)).symm

theorem zeroProposalHistorySource_genealogy (N : ℕ) (R : ℝ) :
    (zeroProposalHistorySource N R).map (zeroHistoryGenealogy N) =
      zeroProposalGenealogySector N R := by
  let F (p : KingmanHistory N × (ℕ → ProposalNoise)) := (p.1, p.2 0)
  have hF : Measurable F := measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
  let S : Set (KingmanHistory N × ProposalNoise) :=
    {p | (spatialStep N R (0, metricTreeFromHistory N p.1) p.2).1 = 1}
  have hS : MeasurableSet S := measurableSet_eq_fun
    (((spatialStep_measurable N R).comp
      ((measurable_const.prodMk ((metricTreeFromHistory_measurable N).comp measurable_fst)).prodMk
        measurable_snd)).fst) measurable_const
  have hstop : MeasurableSet {ω : ℕ → SpatialState N | (ω 1).1 = 1} :=
    measurableSet_eq_fun (measurable_pi_apply 1).fst measurable_const
  have ho :
      (fun p => spatialGenealogyObservation N (historySourceRun N R p)) =ᵐ[
        ((kingmanHistoryLaw N).prod sourceProposalStreamLaw).restrict (F ⁻¹' S)]
      (fun p => zeroHistoryGenealogy N p.1) := by
    filter_upwards [ae_restrict_mem (hS.preimage hF)] with p hp
    exact spatial_observation_zero (historySourceRun N R p) rfl hp
      (historySourceRun_stopped N R p)
  unfold zeroProposalGenealogySector
  rw [← historySourceRun_law N R,
    Measure.restrict_map (historySourceRun_measurable N R) hstop,
    Measure.map_map (spatialGenealogyObservation_measurable N) (historySourceRun_measurable N R)]
  change _ = (((kingmanHistoryLaw N).prod sourceProposalStreamLaw).restrict
    (F ⁻¹' S)).map (fun p => spatialGenealogyObservation N (historySourceRun N R p))
  rw [Measure.map_congr ho]
  unfold zeroProposalHistorySource
  rw [Measure.map_map (zeroHistoryGenealogy_measurable N) measurable_fst,
    ← history_first_mark_law N, Measure.restrict_map hF hS,
    Measure.map_map ((zeroHistoryGenealogy_measurable N).comp measurable_fst) hF]
  rfl
end Rhone.Coalescent.SmcPrime
