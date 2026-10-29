/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeSpatialSourceLaw
public import Rhone.Coalescent.SmcPrimeSpatialSectors
/-!
# History source run: measurability, law, and first-mark laws

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem sourceSpatialRun_joint_measurable (N : ℕ) (R : ℝ) :
    Measurable (fun p : SpatialState N × (ℕ → ProposalNoise) =>
      sourceSpatialRun N R p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro k
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    exact (spatialStep_measurable N R).comp
      (ih.prodMk ((measurable_pi_apply k).comp measurable_snd))

noncomputable def historySourceRun (N : ℕ) (R : ℝ)
    (p : KingmanHistory N × (ℕ → ProposalNoise)) : ℕ → SpatialState N :=
  sourceSpatialRun N R (0, metricTreeFromHistory N p.1) p.2

theorem historySourceRun_measurable (N : ℕ) (R : ℝ) :
    Measurable (historySourceRun N R) :=
  (sourceSpatialRun_joint_measurable N R).comp
    ((measurable_const.prodMk ((metricTreeFromHistory_measurable N).comp measurable_fst)).prodMk
      measurable_snd)

theorem historySourceRun_law (N : ℕ) (R : ℝ) :
    ((kingmanHistoryLaw N).prod sourceProposalStreamLaw).map (historySourceRun N R) =
      (spatialProcess N R).law (spatialInitialLaw N) := by
  have hi : Measurable (fun h : KingmanHistory N => ((0 : ℝ), metricTreeFromHistory N h)) :=
    measurable_const.prodMk (metricTreeFromHistory_measurable N)
  have he : spatialInitialLaw N = (kingmanHistoryLaw N).map
      (fun h => ((0 : ℝ), metricTreeFromHistory N h)) := by
    rw [spatialInitialLaw, kingmanTreeLaw,
      Measure.map_map (show Measurable (fun T : Tree N => ((0 : ℝ), T)) from
        measurable_const.prodMk measurable_id) (metricTreeFromHistory_measurable N)]
    rfl
  ext s hs
  rw [Measure.map_apply (historySourceRun_measurable N R) hs,
    Measure.prod_apply (hs.preimage (historySourceRun_measurable N R)),
    Rhone.MarkovChain.DiscreteProcess.law, Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    he, lintegral_map (show Measurable (fun a : SpatialState N =>
      ((spatialProcess N R).traj a) s) from
        (Measure.measurable_coe hs).comp (Kernel.measurable (spatialProcess N R).traj)) hi]
  apply lintegral_congr
  intro h
  have ht := sourceSpatialRun_law N R (0, metricTreeFromHistory N h)
  have hc := congrArg (fun μ : Measure (ℕ → SpatialState N) => μ s) ht
  rw [Measure.map_apply (sourceSpatialRun_measurable N R _) hs] at hc
  exact hc

theorem historySourceRun_stopped (N : ℕ) (R : ℝ)
    (p : KingmanHistory N × (ℕ → ProposalNoise)) :
    ∀ k, (historySourceRun N R p k).1 = 1 →
      (historySourceRun N R p (k + 1)).1 = 1 := by
  intro k hk
  change (spatialStep N R (historySourceRun N R p k) (p.2 k)).1 = 1
  rw [spatial_step_stopped N R _ _ hk]
  exact hk

theorem source_first_mark_law :
    sourceProposalStreamLaw.map (fun u => u 0) = proposalNoiseLaw :=
  Measure.infinitePi_map_eval (fun _ : ℕ => proposalNoiseLaw) 0

theorem source_first_two_marks_law :
    sourceProposalStreamLaw.map (fun u => (u 0, u 1)) =
      proposalNoiseLaw.prod proposalNoiseLaw := by
  have hi : iIndepFun (fun j (u : ℕ → ProposalNoise) => u j) sourceProposalStreamLaw :=
    iIndepFun_infinitePi (P := fun _ : ℕ => proposalNoiseLaw) (X := fun _ u => u)
      (fun _ => measurable_id)
  rw [(hi.indepFun (show (0 : ℕ) ≠ 1 by omega)).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable]
  rw [source_first_mark_law,
    show sourceProposalStreamLaw.map (fun u => u 1) = proposalNoiseLaw from
      Measure.infinitePi_map_eval (fun _ : ℕ => proposalNoiseLaw) 1]
end Rhone.Coalescent.SmcPrime
