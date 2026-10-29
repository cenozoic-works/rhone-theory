/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeFiniteSourceSector
public import Rhone.Coalescent.SmcPrimeAcceptedProposalDensity
/-!
# The indexed proposal source induces the one-proposal observed sector

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

noncomputable def oneSkeletonGenealogy (N : ℕ) (s : OneSplitSkeleton N) : Genealogy N :=
  fun q i j => if (q.val : ℝ) < s.2.2.2.1 then
    treePairMRCA (metricTreeFromHistory N s.1) i j else treePairMRCA (oneSplitPostTree s) i j

theorem oneSkeletonGenealogy_measurable (N : ℕ) : Measurable (oneSkeletonGenealogy N) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact ((treePairMRCA_measurable N i j).comp
    ((metricTreeFromHistory_measurable N).comp measurable_fst)).piecewise
    (measurableSet_lt measurable_const measurable_snd.snd.snd.fst)
    ((treePairMRCA_measurable N i j).comp (oneSplitPostTree_measurable N))

theorem spatialStep_initial_of_accepted (N : ℕ) (R : ℝ) (T : Tree N) (u : ProposalNoise)
    (hx : (spatialStep N R (0, T) u).1 < 1) :
    0 < treeLength T ∧ spatialStep N R (0, T) u =
      ((proposal R T u).1, (proposal R T u).2.2) := by
  have h0 : ¬ (1 ≤ (0 : ℝ) ∨ R ≤ 0 ∨ treeLength T ≤ 0) := by
    intro h
    have hf : (1 : ℝ) < 1 := by simpa only [spatialStep, h, ite_true] using hx
    exact (lt_irrefl (1 : ℝ)) hf
  have hR : 0 < R := lt_of_not_ge (fun h => h0 (Or.inr (Or.inl h)))
  have hL : 0 < treeLength T := lt_of_not_ge (fun h => h0 (Or.inr (Or.inr h)))
  have hd := (spatialStep_initial_accepted R T hR hL u).mp hx
  exact ⟨hL, by simp only [spatialStep, h0, ite_false, zero_add, hd, ite_true]⟩

theorem oneSkeletonGenealogy_source_ae (N : ℕ) (R : ℝ) :
    (fun p : KingmanHistory N × ProposalNoise × ProposalNoise =>
      oneSkeletonGenealogy N (indexedProposal N R p.1 p.2.1)) =ᵐ[
      ((kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw)).restrict
        (historyOneStop N R)] firstProposalGenealogy N R := by
  have hm : ∀ᵐ p ∂(kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw),
      ∀ i, p.2.1 i ∈ Set.Ioo 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := proposalNoiseLaw) (ν := proposalNoiseLaw)).comp
      (Measure.quasiMeasurePreserving_snd (μ := kingmanHistoryLaw N)
        (ν := proposalNoiseLaw.prod proposalNoiseLaw))).ae proposalNoiseLaw_ae_marks
  filter_upwards [ae_restrict_of_ae hm,
    ae_restrict_mem (historyOneStop_measurable N R)] with p hp hs
  have hx : (spatialStep N R (0, metricTreeFromHistory N p.1) p.2.1).1 < 1 := hs.1
  obtain ⟨hL, he⟩ := spatialStep_initial_of_accepted N R (metricTreeFromHistory N p.1) p.2.1 hx
  obtain ⟨s, t, hc, _⟩ := cut_point_extant_clade (metricTreeFromHistory N p.1) hL
    (p.2.1 1) (p.2.1 2) ⟨(hp 1).1.le, (hp 1).2⟩ ⟨(hp 2).1.le, (hp 2).2⟩
  have ht := indexedProposal_postTree N R p.1 p.2.1 ⟨s, t, hc⟩
  funext q i j
  simp only [oneSkeletonGenealogy, firstProposalGenealogy, historyFirstStep, he,
    ht]
  rfl

theorem oneProposalSkeletonSource_genealogy (N : ℕ) (R : ℝ) :
    (oneProposalSkeletonSource N R).map (oneSkeletonGenealogy N) =
      oneProposalGenealogySector N R := by
  have hp : Measurable (fun p : KingmanHistory N × ProposalNoise × ProposalNoise =>
      indexedProposal N R p.1 p.2.1) :=
    (indexedProposal_measurable N R).comp (measurable_fst.prodMk measurable_snd.fst)
  rw [oneProposalSkeletonSource,
    Measure.map_map (oneSkeletonGenealogy_measurable N) hp,
    ← firstProposalGenealogy_law N R]
  exact Measure.map_congr (oneSkeletonGenealogy_source_ae N R)
end Rhone.Coalescent.SmcPrime
