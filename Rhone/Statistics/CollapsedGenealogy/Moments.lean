/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Object
public import Rhone.Statistics.ThreeSiteSeparator.ScoreSymmetry

/-! # Extraction of arbitrary pair-score words from joint blocks -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator

abbrev NonnegativeJoint (μ : Measure Joint) : Prop := ∀ᵐ g ∂μ, 0 ≤ g.1.1 ∧ 0 ≤ g.1.2

theorem fixed_nonneg {K L : ℕ} (π : Roots K L) {k : ℝ} (hk : 0 ≤ k)
    (g : Joint) (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2) (x : Panel K L) :
    0 ≤ fixedTopology π k g.1 g.2 x := by
  exact Finset.prod_nonneg fun s _ => site_nonneg _ (π.nonneg s) hk hg _

theorem fixed_integrable {K L : ℕ} (hK : 0 < K) (π : Roots K L) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) [IsFiniteMeasure μ] (hμ : NonnegativeJoint μ) (x : Panel K L) :
    Integrable (fun g => fixedTopology π k g.1 g.2 x) μ := by
  refine Integrable.of_bound (joint_kernel_measurable π k x).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with g hg
  rw [Real.norm_eq_abs, abs_of_nonneg (fixed_nonneg π hk g hg x)]
  rw [← fixedTopology_sum hK π k g.1 g.2]
  exact Finset.single_le_sum (fun y _ => fixed_nonneg π hk g hg y) (Finset.mem_univ x)

theorem joint_mass_nonneg {K L : ℕ} (π : Roots K L) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) (hμ : NonnegativeJoint μ) (x : Panel K L) :
    0 ≤ jointMass π k μ x := by
  apply integral_nonneg_of_ae
  filter_upwards [hμ] with g hg
  exact fixed_nonneg π hk g hg x

theorem joint_law_singleton {K L : ℕ} (π : Roots K L) (k : ℝ)
    (μ : Measure Joint) (x : Panel K L) :
    jointSequenceLaw π k μ {x} = ENNReal.ofReal (jointMass π k μ x) := by
  simp [jointSequenceLaw, Pi.single_apply, mul_ite]

theorem equal_laws_equal_masses {K L : ℕ} (π : Roots K L) {k l : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (μ ν : Measure Joint)
    (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν)
    (he : jointSequenceLaw π k μ = jointSequenceLaw π l ν) (x : Panel K L) :
    jointMass π k μ x = jointMass π l ν x := by
  have hh := congrArg (fun M : Measure (Panel K L) => M {x}) he
  simp only [joint_law_singleton] at hh
  have ht := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (joint_mass_nonneg π hk μ hμ x),
    ENNReal.toReal_ofReal (joint_mass_nonneg π hl ν hν x)] using ht

theorem word_moment {K L : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) [IsFiniteMeasure μ] (hμ : NonnegativeJoint μ) (w : Fin L → Fin 3) :
    (∑ x : Panel K L, (∏ s, uScore (w s) (x s)) *
      jointMass (uniformBlockRoots K L (by omega)) k μ x) =
      ∫ g, ∏ s, pairMeans (Real.exp (-k * g.1.1))
        (Real.exp (-k * (g.1.1 + g.1.2))) g.2 (w s) ∂μ := by
  unfold jointMass
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun x _ =>
    (fixed_integrable (by omega) _ hk μ hμ x).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [fixedTopology_product_scores]
  apply Finset.prod_congr rfl
  intro s _
  exact oriented_pair_mean hK k g.1 g.2 (w s)

end Rhone.Statistics.CollapsedGenealogy
