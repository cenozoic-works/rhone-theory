/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingPrefix

/-! # The three-sample witness across a coalescence-free migration window -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma witness_eq_of_histories (k : ℕ) (c q c' q' : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hc' : Continuous c') (hq' : Continuous q')
    {T : ℝ} (hT : 0 ≤ T) (he : ∀ u ∈ Icc 0 T, c u = c' u ∧ q u = q' u) :
    witness k c q T = witness k c' q' T := by
  have hp := inhomogeneousTransition_eq_of_eqOn
    (fun u => threeGenerator k (c u) (q u)) (fun u => threeGenerator k (c' u) (q' u))
    (preGenerator_continuous k c q hc hq) (preGenerator_continuous k c' q' hc' hq') hT
    (fun u hu => by dsimp only; rw [(he u hu).1, (he u hu).2])
  have hr : preRow k c q T = preRow k c' q' T := congrArg (fun M => M 0) hp
  simp only [witness, survival, hr]

theorem witness_positive_after_silent_window (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hbefore : ∀ u ∈ Ioo 0 a, q u = 0)
    (hsilent : ∀ u ∈ Icc a (a + T), c u = 0)
    (hQ : 0 < ∫ u in (0 : ℝ)..T, q (a + u)) :
    0 < witness k c q (a + T) := by
  rw [witness_after_zero_migration_prefix k c q hc hq ha hbefore]
  apply mul_pos (sq_pos_of_pos (initial_pre_coordinate_positive k c q hc hq hqn ha))
  have he := witness_eq_of_histories k (fun u => c (a + u)) (fun u => q (a + u))
    (fun _ => 0) (fun u => q (a + u))
    (hc.comp (continuous_const.add continuous_id)) (hq.comp (continuous_const.add continuous_id))
    continuous_const (hq.comp (continuous_const.add continuous_id)) hT
    (fun u hu => ⟨hsilent (a + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩)
  rw [he]
  exact witness_positive_silent_migration k (fun u => q (a + u))
    (hq.comp (continuous_const.add continuous_id)) hQ

lemma witness_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    Continuous (witness k c q) := by
  have hU : Continuous (fun t : ℝ => inhomogeneousTransition
      (fun u => productGenerator k (c u) (q u)) 0 t) :=
    (inhomogeneousTransition_continuous _ (productGenerator_continuous k c q hc hq)).comp
      (continuous_const.prodMk continuous_id)
  change Continuous (fun t => witness k c q t)
  simp_rw [witness_eq_product_output k c q hc hq]
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp ((continuous_apply (0, 0)).comp hU))).mul continuous_const

lemma witness_positive_right (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    {a : ℝ} (ha : 0 < witness k c q a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → 0 < witness k c q (a + t) := by
  have he := (witness_continuous k c q hc hq).continuousAt.eventually (eventually_gt_nhds ha)
  obtain ⟨δ, hδ, hpos⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun t ht htδ => hpos ?_⟩
  simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht] using htδ

end Rhone.Statistics.Identifiability.ThreeTimeVarying
