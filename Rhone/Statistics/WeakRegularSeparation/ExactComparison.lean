/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.Collapse
public import Rhone.Statistics.CollapsedGenealogy.Equivalence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Exact candidate comparison without imposing positive internal branches on the source -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeTipSites ThreeSiteSeparator

theorem scale_injective {k : ℝ} (hk : k ≠ 0) : Function.Injective (scale k) := by
  intro g h he
  have hu := congrArg (fun x : Joint => x.1.1) he
  have hv := congrArg (fun x : Joint => x.1.2) he
  have hq := congrArg (fun x : Joint => x.2) he
  exact Prod.ext (Prod.ext (mul_left_cancel₀ hk hu) (mul_left_cancel₀ hk hv)) hq

theorem scale_collapse_commute {k : ℝ} (hk : k ≠ 0) :
    collapse ∘ scale k = scale k ∘ collapse := by
  funext g
  simp [Function.comp_apply, collapse, scale, mul_eq_zero, hk]

theorem object_eq_iff_collapsed_eq {k : ℝ} (hk : k ≠ 0) (μ ν : Measure Joint) :
    object k μ = object k ν ↔ μ.map collapse = ν.map collapse := by
  have he (ρ : Measure Joint) : object k ρ = (ρ.map collapse).map (scale k) := by
    rw [Measure.map_map (scale_measurable k) collapse_measurable]
    unfold object
    rw [scale_collapse_commute hk]
  rw [he μ, he ν]
  exact (scale_measurable k).measurableEmbedding (scale_injective hk) |>.map_injective.eq_iff

theorem all_blocks_against_positive_candidate {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 < k)
    (μ ν : Measure Joint) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν) (hvν : ∀ᵐ g ∂ν, 0 < g.1.2) :
    (∀ L : ℕ, jointSequenceLaw (uniformBlockRoots K L (by omega)) k μ =
      jointSequenceLaw (uniformBlockRoots K L (by omega)) k ν) ↔ μ = ν := by
  rw [all_blocks_iff_collapsed_joint_eq hK hk.le hk.le μ ν hμ hν,
    object_eq_iff_collapsed_eq hk.ne', collapsed_eq_iff_joint_eq μ ν hvν]

end Rhone.Statistics.WeakRegularSeparation
