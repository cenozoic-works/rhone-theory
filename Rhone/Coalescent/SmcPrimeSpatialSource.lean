/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialGeometrySupport
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Independent proposal source for the full spatial recursion and its budget

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Filter

noncomputable def sourceProposalStreamLaw : Measure (ℕ → ProposalNoise) :=
  Measure.infinitePi (fun _ : ℕ => proposalNoiseLaw)

instance : IsProbabilityMeasure sourceProposalStreamLaw := by
  unfold sourceProposalStreamLaw
  infer_instance

noncomputable def sourceSpatialRun (N : ℕ) (R : ℝ) (z : SpatialState N)
    (u : ℕ → ProposalNoise) : ℕ → SpatialState N
  | 0 => z
  | k + 1 => spatialStep N R (sourceSpatialRun N R z u k) (u k)

theorem sourceSpatialRun_eval_measurable (N : ℕ) (R : ℝ) (z : SpatialState N) (k : ℕ) :
    Measurable (fun u => sourceSpatialRun N R z u k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (spatialStep_measurable N R).comp (ih.prodMk (measurable_pi_apply k))

theorem sourceSpatialRun_measurable (N : ℕ) (R : ℝ) (z : SpatialState N) :
    Measurable (sourceSpatialRun N R z) :=
  measurable_pi_iff.mpr (sourceSpatialRun_eval_measurable N R z)

theorem sourceSpatialRun_geometry {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) (u : ℕ → ProposalNoise)
    (hu : ∀ k i, u k i ∈ Set.Ioo 0 1) (k : ℕ) :
    TreeNormalized (sourceSpatialRun N R z u k).2 ∧
    TreeNonnegative (sourceSpatialRun N R z u k).2 ∧
    TreeChronology (sourceSpatialRun N R z u k).2 ∧
    treeLength (sourceSpatialRun N R z u k).2 ≤
      treeLength z.2 + 2 * ∑ j ∈ Finset.range k, -Real.log (u j 3) := by
  induction k with
  | zero =>
    simp only [sourceSpatialRun, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    exact ⟨hnorm, hnonneg, hchron, le_rfl⟩
  | succ k ih =>
    have hg := spatial_step_tree_geometry R (sourceSpatialRun N R z u k) (u k)
      hN ih.1 ih.2.1 ih.2.2.1 (hu k)
    refine ⟨hg.1, hg.2.1, hg.2.2.1, ?_⟩
    simp only [Finset.sum_range_succ]
    change treeLength (spatialStep N R (sourceSpatialRun N R z u k) (u k)).2 ≤ _
    linarith [hg.2.2.2.2, ih.2.2.2]

theorem sourceProposalStreamLaw_ae_marks :
    ∀ᵐ u ∂sourceProposalStreamLaw, ∀ k i, u k i ∈ Set.Ioo 0 1 := by
  apply ae_all_iff.mpr
  intro k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => proposalNoiseLaw) k)
    |>.quasiMeasurePreserving.ae proposalNoiseLaw_ae_marks

theorem sourceBudget_lintegral (i : Fin 5) (k : ℕ) :
    (∫⁻ u, ENNReal.ofReal (-Real.log (u k i)) ∂sourceProposalStreamLaw) = 1 := by
  have hm := (measurePreserving_eval
    (fun _ : Fin 5 => Rhone.Coalescent.IntervalProcess.unitUniform) i).comp
    (measurePreserving_eval_infinitePi (fun _ : ℕ => proposalNoiseLaw) k)
  rw [← inverse_log_budget_mean, ← hm.map_eq, lintegral_map (by fun_prop) (by fun_prop)]
  rfl

theorem sourceBudget_nonnegative (i : Fin 5) (k : ℕ) :
    ∀ᵐ u ∂sourceProposalStreamLaw, 0 ≤ -Real.log (u k i) := by
  filter_upwards [sourceProposalStreamLaw_ae_marks] with u hu
  exact neg_nonneg.mpr (Real.log_nonpos (hu k i).1.le (hu k i).2.le)

theorem sourceBudget_integrable (i : Fin 5) (k : ℕ) :
    Integrable (fun u => -Real.log (u k i)) sourceProposalStreamLaw := by
  refine ⟨(show Measurable (fun u : ℕ → ProposalNoise => -Real.log (u k i)) by
      fun_prop).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have heq : (fun u => ENNReal.ofReal ‖-Real.log (u k i)‖) =ᵐ[sourceProposalStreamLaw]
      (fun u => ENNReal.ofReal (-Real.log (u k i))) := by
    filter_upwards [sourceBudget_nonnegative i k] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg hu]
  rw [lintegral_congr_ae heq, sourceBudget_lintegral]
  exact ENNReal.one_lt_top

theorem sourceBudget_integral (i : Fin 5) (k : ℕ) :
    (∫ u, -Real.log (u k i) ∂sourceProposalStreamLaw) = 1 := by
  have hm : Measurable (fun u : ℕ → ProposalNoise => -Real.log (u k i)) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (sourceBudget_nonnegative i k)
      hm.aestronglyMeasurable,
    sourceBudget_lintegral, ENNReal.toReal_one]

theorem sourceBudget_strong_law (i : Fin 5) :
    ∀ᵐ u ∂sourceProposalStreamLaw,
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, -Real.log (u k i)) / n)
        atTop (nhds 1) := by
  have hind : iIndepFun (fun k (u : ℕ → ProposalNoise) => -Real.log (u k i))
      sourceProposalStreamLaw :=
    iIndepFun_infinitePi (P := fun _ : ℕ => proposalNoiseLaw)
      (X := fun _ u => -Real.log (u i)) (by intro k; fun_prop)
  have hid (k : ℕ) : IdentDistrib (fun u : ℕ → ProposalNoise => -Real.log (u k i))
      (fun u : ℕ → ProposalNoise => -Real.log (u 0 i))
      sourceProposalStreamLaw sourceProposalStreamLaw := by
    have heval : IdentDistrib (fun u : ℕ → ProposalNoise => u k) (fun u => u 0)
        sourceProposalStreamLaw sourceProposalStreamLaw :=
      ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
        exact (Measure.infinitePi_map_eval (fun _ : ℕ => proposalNoiseLaw) k).trans
          (Measure.infinitePi_map_eval (fun _ : ℕ => proposalNoiseLaw) 0).symm⟩
    exact heval.comp (by fun_prop : Measurable (fun u : ProposalNoise => -Real.log (u i)))
  simpa only [sourceBudget_integral] using
    strong_law_ae_real (fun k (u : ℕ → ProposalNoise) => -Real.log (u k i))
      (sourceBudget_integrable i 0) (fun k j hkj => hind.indepFun hkj) hid

end Rhone.Coalescent.SmcPrime
