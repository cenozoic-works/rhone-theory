/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeReferenceSkeleton
public import Rhone.Coalescent.SmcPrimeProposalSupport
public import Rhone.Coalescent.SmcPrimeSpatialStopMass

/-!
# The indexed SMC′ proposal, its post-regraft tree, and the one-proposal source density

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem forgetCutIndex_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × (ℕ × ℝ) => forgetCutIndex p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  let P := (Fin m → Branch N) × (ℕ × ℝ)
  let f (k : ℕ) (p : P) : Finset (Fin N) × ℝ :=
    if h : k < m then ((p.1 ⟨k, h⟩).1, p.2.2) else (∅, 0)
  have hf (k : ℕ) : Measurable (f k) := by
    by_cases h : k < m
    · simp only [f, dite_eq_left h]
      exact ((measurable_pi_apply (⟨k, h⟩ : Fin m)).comp measurable_fst).fst.prodMk
        measurable_snd.snd
    · simp only [f, dite_eq_right h]
      exact measurable_const
  convert measurable_countable_choice (fun p : P => p.2.1) measurable_snd.fst f hf using 1
  funext p
  rfl

theorem regraft_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × Finset (Fin N) × Finset (Fin N) × ℝ × ℝ =>
      regraft p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  exact regraftFiber_measurable N m

noncomputable def indexedProposal (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (u : ProposalNoise) : OneSplitSkeleton N :=
  let T := metricTreeFromHistory N h
  let bt := indexedCutValue T (u 1, u 2)
  let a := attachmentTime T bt.2 (-Real.log (u 3))
  (h, bt.1, bt.2, (proposal R T u).1, a, attachmentTarget T a (u 4))

theorem indexedProposal_measurable (N : ℕ) (R : ℝ) :
    Measurable (fun p : KingmanHistory N × ProposalNoise =>
      indexedProposal N R p.1 p.2) := by
  let P := KingmanHistory N × ProposalNoise
  have hT : Measurable (fun p : P => metricTreeFromHistory N p.1) :=
    (metricTreeFromHistory_measurable N).comp measurable_fst
  have hb : Measurable (fun p : P => indexedCutValue (metricTreeFromHistory N p.1)
      (p.2 1, p.2 2)) :=
    (indexedCutValue_joint_measurable N).comp (hT.prodMk
      (((measurable_pi_apply 1).comp measurable_snd).prodMk
        ((measurable_pi_apply 2).comp measurable_snd)))
  have ha : Measurable (fun p : P =>
      let a := attachmentTime (metricTreeFromHistory N p.1)
        (indexedCutValue (metricTreeFromHistory N p.1) (p.2 1, p.2 2)).2 (-Real.log (p.2 3))
      (a, attachmentTarget (metricTreeFromHistory N p.1) a (p.2 4))) :=
    (attachmentMark_joint_measurable N).comp (hT.prodMk (hb.snd.prodMk
      (((measurable_pi_apply 3).comp measurable_snd).prodMk
        ((measurable_pi_apply 4).comp measurable_snd))))
  have hx := ((proposal_measurable N R).comp (hT.prodMk measurable_snd)).fst
  exact measurable_fst.prodMk (hb.fst.prodMk (hb.snd.prodMk (hx.prodMk ha)))

noncomputable def oneSplitPostTree {N : ℕ} (s : OneSplitSkeleton N) : Tree N :=
  let T := metricTreeFromHistory N s.1
  regraft T (forgetCutIndex T (s.2.1, s.2.2.1)).1
    s.2.2.2.2.2 s.2.2.1 s.2.2.2.2.1

theorem oneSplitPostTree_measurable (N : ℕ) : Measurable (@oneSplitPostTree N) := by
  have hT : Measurable (fun s : OneSplitSkeleton N => metricTreeFromHistory N s.1) :=
    (metricTreeFromHistory_measurable N).comp measurable_fst
  have hc : Measurable (fun s : OneSplitSkeleton N =>
      forgetCutIndex (metricTreeFromHistory N s.1) (s.2.1, s.2.2.1)) :=
    (forgetCutIndex_joint_measurable N).comp
    (hT.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))
  convert (regraft_joint_measurable N).comp (hT.prodMk
    (hc.fst.prodMk (measurable_snd.snd.snd.snd.snd.prodMk
      (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd.snd.fst)))) using 1
  funext s
  rfl

noncomputable def oneProposalSkeletonSource (N : ℕ) (R : ℝ) :
    Measure (OneSplitSkeleton N) :=
  (((kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw)).restrict
    {p | let z := spatialStep N R (0, metricTreeFromHistory N p.1) p.2.1
         z.1 < 1 ∧ (spatialStep N R z p.2.2).1 = 1}).map
    (fun p => indexedProposal N R p.1 p.2.1)

noncomputable def oneProposalDensity (N : ℕ) (R : ℝ)
    (s : OneSplitSkeleton N) : ℝ≥0∞ :=
  ENNReal.ofReal (R / 2 * Real.exp (-(R / 2 *
    (s.2.2.2.1 * treeLength (metricTreeFromHistory N s.1) +
      (1 - s.2.2.2.1) * treeLength (oneSplitPostTree s)))))

theorem oneProposalDensity_measurable (N : ℕ) (R : ℝ) :
    Measurable (oneProposalDensity N R) := by
  have hL : Measurable (fun s : OneSplitSkeleton N =>
      treeLength (metricTreeFromHistory N s.1)) := (treeLength_joint_measurable N).comp
    ((metricTreeFromHistory_measurable N).comp measurable_fst)
  have hL' := (treeLength_joint_measurable N).comp (oneSplitPostTree_measurable N)
  exact (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_snd.snd.snd.fst.mul hL).add
      ((measurable_const.sub measurable_snd.snd.snd.fst).mul hL'))).neg)).ennreal_ofReal

theorem oneProposalSkeletonSource_zero (N : ℕ) : oneProposalSkeletonSource N 0 = 0 := by
  simp [oneProposalSkeletonSource, spatialStep]

theorem oneProposalDensity_zero (N : ℕ) : oneProposalDensity N 0 = 0 := by
  funext s
  simp [oneProposalDensity]
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
open scoped ENNReal

theorem spatialClock_density (q : ℝ) (hq : 0 < q) :
    unitUniform.map (fun u => -Real.log u / q) =
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (q * Real.exp (-q * x))) := by
  simpa only [zero_sub, sub_zero, neg_div] using inverseClock_shift_density q hq 0

theorem spatialClock_accepted_density (q : ℝ) (hq : 0 < q) :
    (unitUniform.map (fun u => -Real.log u / q)).restrict (Set.Iio 1) =
      unitUniform.withDensity (fun x => ENNReal.ofReal (q * Real.exp (-q * x))) := by
  rw [spatialClock_density q hq, restrict_withDensity measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  congr 1
  change volume.restrict (Set.Iio (1 : ℝ) ∩ Set.Ioi 0) = volume.restrict (Set.Ioo 0 1)
  congr 1
  ext x
  exact and_comm

theorem proposal_fst_eq {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise) :
    (proposal R T u).1 = -Real.log (u 0) / (R / 2 * treeLength T) := by
  unfold proposal
  cases cutPoint T (u 1) (u 2) <;> rfl

theorem indexedProposal_source (N : ℕ) (R : ℝ) (h : KingmanHistory N)
    (u : ProposalNoise) :
    indexedProposal N R h u = oneSplitReferenceSourceMap N h
      ((u 1, u 2), (-Real.log (u 0) / (R / 2 * treeLength (metricTreeFromHistory N h)),
        (u 3, u 4))) := by
  simp only [indexedProposal, oneSplitReferenceSourceMap, oneSplitTailMap,
    proposal_fst_eq]
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem proposalNoiseLaw_cut_clock_attachment :
    proposalNoiseLaw.map (fun u => ((u 1, u 2), (u 0, (u 3, u 4)))) =
      (unitUniform.prod unitUniform).prod
        (unitUniform.prod (unitUniform.prod unitUniform)) := by
  apply Measure.ext_prod₃
  intro s t v hs ht hv
  have hf : Measurable (fun u : ProposalNoise => ((u 1, u 2), (u 0, (u 3, u 4)))) :=
    by fun_prop
  have hg : Measurable (fun u : ProposalNoise => (u 0, ((u 1, u 2), (u 3, u 4)))) :=
    by fun_prop
  rw [Measure.map_apply hf (hs.prod (ht.prod hv))]
  have he : (fun u : ProposalNoise => ((u 1, u 2), (u 0, (u 3, u 4)))) ⁻¹'
      (s ×ˢ (t ×ˢ v)) =
      (fun u : ProposalNoise => (u 0, ((u 1, u 2), (u 3, u 4)))) ⁻¹'
        (t ×ˢ (s ×ˢ v)) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_prod]
    tauto
  rw [he, ← Measure.map_apply hg (ht.prod (hs.prod hv)), proposalNoiseLaw_grouped]
  simp only [Measure.prod_prod]
  ac_rfl

theorem proposalNoiseLaw_cut_distance_attachment (q : ℝ) :
    proposalNoiseLaw.map (fun u => ((u 1, u 2), (-Real.log (u 0) / q, (u 3, u 4)))) =
      (unitUniform.prod unitUniform).prod
        ((unitUniform.map (fun u => -Real.log u / q)).prod (unitUniform.prod unitUniform)) := by
  let F (p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) := (p.1, (-Real.log p.2.1 / q, p.2.2))
  have hF : Measurable F := by fun_prop
  change proposalNoiseLaw.map
    (F ∘ fun u => ((u 1, u 2), (u 0, (u 3, u 4)))) = _
  rw [← Measure.map_map hF (by fun_prop), proposalNoiseLaw_cut_clock_attachment]
  change ((unitUniform.prod unitUniform).prod
    (unitUniform.prod (unitUniform.prod unitUniform))).map
      (Prod.map id (Prod.map (fun u => -Real.log u / q) id)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
end Rhone.Coalescent.SmcPrime
