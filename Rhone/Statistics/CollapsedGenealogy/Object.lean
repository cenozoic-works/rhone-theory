/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Boundary

/-! # Mutation-scaled joint object: only zero internal labels collapse -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator
open Identifiability.EqualRatesMutation

def collapse (g : Joint) : Joint := (g.1, if g.1.2 = 0 then 0 else g.2)
def scale (k : ℝ) (g : Joint) : Joint := ((k * g.1.1, k * g.1.2), g.2)
def object (k : ℝ) (μ : Measure Joint) : Measure Joint := Measure.map (collapse ∘ scale k) μ

theorem collapse_measurable : Measurable collapse := by
  unfold collapse
  exact measurable_fst.prodMk
    (Measurable.ite (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const)
      measurable_const measurable_snd)

theorem scale_measurable (k : ℝ) : Measurable (scale k) := by
  unfold scale
  fun_prop

theorem transition_scale (K : ℕ) (k t : ℝ) : transition K k t = transition K 1 (k * t) := by
  have he : -(k / 2) * t = -(1 / 2) * (k * t) := by ring
  simp only [transition, he]

theorem site_scale {K : ℕ} (π : Fin K → ℝ) (k : ℝ) (t : ℝ × ℝ) (x : Triple K) :
    site K π k t x = site K π 1 (k * t.1, k * t.2) x := by
  unfold site
  simp_rw [transition_scale K k]
  rw [mul_add]

theorem fixed_scale {K L : ℕ} (π : Roots K L) (k : ℝ) (g : Joint) (x : Panel K L) :
    fixedTopology π k g.1 g.2 x = fixedTopology π 1 (scale k g).1 (scale k g).2 x := by
  unfold fixedTopology scale
  apply Finset.prod_congr rfl
  intro s _
  exact site_scale _ _ _ _

theorem fixed_collapse {K L : ℕ} (hK : 0 < K) (g : Joint) (x : Panel K L) :
    fixedTopology (uniformBlockRoots K L hK) 1 (collapse g).1 (collapse g).2 x =
      fixedTopology (uniformBlockRoots K L hK) 1 g.1 g.2 x := by
  unfold collapse
  by_cases hz : g.1.2 = 0
  · rw [ite_eq_left hz]
    have he : g.1 = (g.1.1, 0) := Prod.ext rfl hz
    rw [he]
    exact star_fixed_topology hK 1 g.1.1 0 g.2 x
  · rw [ite_eq_right hz]

theorem joint_kernel_measurable {K L : ℕ} (π : Roots K L) (k : ℝ) (x : Panel K L) :
    Measurable (fun g : Joint => fixedTopology π k g.1 g.2 x) := by
  apply measurable_from_prod_countable_left
  intro q
  unfold fixedTopology site transition
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem sequence_law_object {K L : ℕ} (hK : 0 < K) (k : ℝ) (μ : Measure Joint) :
    jointSequenceLaw (uniformBlockRoots K L hK) k μ =
      jointSequenceLaw (uniformBlockRoots K L hK) 1 (object k μ) := by
  unfold jointSequenceLaw
  congr 1
  funext x
  unfold jointMass object
  rw [integral_map (collapse_measurable.comp (scale_measurable k)).aemeasurable
    (joint_kernel_measurable _ 1 x).aestronglyMeasurable]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [Function.comp_apply, fixed_collapse hK]
  exact fixed_scale _ k g x

theorem collapsed_joint_eq_all_blocks (k l : ℝ) (μ ν : Measure Joint)
    (he : object k μ = object l ν) : ∀ K L : ℕ, ∀ hK : 0 < K,
      jointSequenceLaw (uniformBlockRoots K L hK) k μ =
        jointSequenceLaw (uniformBlockRoots K L hK) l ν := by
  intro K L hK
  rw [sequence_law_object hK k μ, sequence_law_object hK l ν, he]

end Rhone.Statistics.CollapsedGenealogy
