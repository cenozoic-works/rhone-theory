/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeSourcePath
/-!
# The first two independent proposal marks induce the existing one-proposal observed sector

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem history_first_two_marks_law (N : ℕ) :
    ((kingmanHistoryLaw N).prod sourceProposalStreamLaw).map
      (fun p => (p.1, p.2 0, p.2 1)) =
      (kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw) := by
  simpa only [Measure.map_id, source_first_two_marks_law, Prod.map_def, id_eq] using
    (Measure.map_prod_map (kingmanHistoryLaw N) sourceProposalStreamLaw measurable_id
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))).symm

noncomputable def historyFirstStep (N : ℕ) (R : ℝ)
    (p : KingmanHistory N × ProposalNoise × ProposalNoise) : SpatialState N :=
  spatialStep N R (0, metricTreeFromHistory N p.1) p.2.1

theorem historyFirstStep_measurable (N : ℕ) (R : ℝ) : Measurable (historyFirstStep N R) :=
  (spatialStep_measurable N R).comp
    ((measurable_const.prodMk ((metricTreeFromHistory_measurable N).comp measurable_fst)).prodMk
      measurable_snd.fst)

def historyOneStop (N : ℕ) (R : ℝ) : Set (KingmanHistory N × ProposalNoise × ProposalNoise) :=
  {p | (historyFirstStep N R p).1 < 1 ∧
    (spatialStep N R (historyFirstStep N R p) p.2.2).1 = 1}

theorem historyOneStop_measurable (N : ℕ) (R : ℝ) : MeasurableSet (historyOneStop N R) :=
  (measurableSet_lt (historyFirstStep_measurable N R).fst measurable_const).inter
    (measurableSet_eq_fun (((spatialStep_measurable N R).comp
      ((historyFirstStep_measurable N R).prodMk measurable_snd.snd)).fst) measurable_const)

noncomputable def firstProposalGenealogy (N : ℕ) (R : ℝ)
    (p : KingmanHistory N × ProposalNoise × ProposalNoise) : Genealogy N :=
  fun q i j => if (q.val : ℝ) < (historyFirstStep N R p).1 then
    treePairMRCA (metricTreeFromHistory N p.1) i j
  else treePairMRCA (historyFirstStep N R p).2 i j

theorem firstProposalGenealogy_measurable (N : ℕ) (R : ℝ) :
    Measurable (firstProposalGenealogy N R) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact ((treePairMRCA_measurable N i j).comp
    ((metricTreeFromHistory_measurable N).comp measurable_fst)).piecewise
    (measurableSet_lt measurable_const (historyFirstStep_measurable N R).fst)
    ((treePairMRCA_measurable N i j).comp (historyFirstStep_measurable N R).snd)

theorem firstProposalGenealogy_law (N : ℕ) (R : ℝ) :
    (((kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw)).restrict
      (historyOneStop N R)).map (firstProposalGenealogy N R) =
      oneProposalGenealogySector N R := by
  let F (p : KingmanHistory N × (ℕ → ProposalNoise)) := (p.1, p.2 0, p.2 1)
  have hF : Measurable F := measurable_fst.prodMk
    (((measurable_pi_apply 0).comp measurable_snd).prodMk
      ((measurable_pi_apply 1).comp measurable_snd))
  have hstop : MeasurableSet {ω : ℕ → SpatialState N | (ω 1).1 < 1 ∧ (ω 2).1 = 1} := by
    have h1 : Measurable (fun ω : ℕ → SpatialState N => (ω 1).1) :=
      (measurable_pi_apply 1).fst
    have h2 : Measurable (fun ω : ℕ → SpatialState N => (ω 2).1) :=
      (measurable_pi_apply 2).fst
    exact (measurableSet_lt h1 measurable_const).inter
      (measurableSet_eq_fun h2 measurable_const)
  have ho :
      (fun p => spatialGenealogyObservation N (historySourceRun N R p)) =ᵐ[
        ((kingmanHistoryLaw N).prod sourceProposalStreamLaw).restrict
          (F ⁻¹' historyOneStop N R)]
      (fun p => firstProposalGenealogy N R (F p)) := by
    filter_upwards [ae_restrict_mem ((historyOneStop_measurable N R).preimage hF)] with p hp
    exact spatial_observation_one (historySourceRun N R p) rfl hp.1 hp.2
      (historySourceRun_stopped N R p)
  unfold oneProposalGenealogySector
  rw [← historySourceRun_law N R,
    Measure.restrict_map (historySourceRun_measurable N R) hstop,
    Measure.map_map (spatialGenealogyObservation_measurable N) (historySourceRun_measurable N R)]
  change _ = (((kingmanHistoryLaw N).prod sourceProposalStreamLaw).restrict
    (F ⁻¹' historyOneStop N R)).map
      (fun p => spatialGenealogyObservation N (historySourceRun N R p))
  rw [Measure.map_congr ho, ← history_first_two_marks_law N,
    Measure.restrict_map hF (historyOneStop_measurable N R),
    Measure.map_map (firstProposalGenealogy_measurable N R) hF]
  rfl
end Rhone.Coalescent.SmcPrime
