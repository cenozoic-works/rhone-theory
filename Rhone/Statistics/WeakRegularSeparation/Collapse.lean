/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Object

/-! # Boundary lemma: comparison with a strictly positive internal branch loses no labels -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy

theorem collapse_eq_self_of_positive (g : Joint) (hg : 0 < g.1.2) : collapse g = g := by
  simp [collapse, ne_of_gt hg]

theorem collapse_map_eq_self (μ : Measure Joint) (hμ : ∀ᵐ g ∂μ, 0 < g.1.2) :
    μ.map collapse = μ := by
  calc
    μ.map collapse = μ.map id := Measure.map_congr (hμ.mono fun g hg =>
      collapse_eq_self_of_positive g hg)
    _ = μ := Measure.map_id

theorem positive_of_collapsed_eq (μ ν : Measure Joint)
    (hν : ∀ᵐ g ∂ν, 0 < g.1.2) (he : μ.map collapse = ν.map collapse) :
    ∀ᵐ g ∂μ, 0 < g.1.2 := by
  have hm : MeasurableSet {g : Joint | 0 < g.1.2} := by measurability
  have hv : ∀ᵐ g ∂ν.map collapse, 0 < g.1.2 :=
    (ae_map_iff collapse_measurable.aemeasurable hm).mpr hν
  rw [← he] at hv
  exact (ae_map_iff collapse_measurable.aemeasurable hm).mp hv

theorem collapsed_eq_iff_joint_eq (μ ν : Measure Joint)
    (hν : ∀ᵐ g ∂ν, 0 < g.1.2) : μ.map collapse = ν.map collapse ↔ μ = ν := by
  constructor
  · intro he
    have hμ := positive_of_collapsed_eq μ ν hν he
    rwa [collapse_map_eq_self μ hμ, collapse_map_eq_self ν hν] at he
  · rintro rfl
    rfl

end Rhone.Statistics.WeakRegularSeparation
