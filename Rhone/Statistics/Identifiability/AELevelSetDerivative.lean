/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.DimOne
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Tactic

/-! # Derivatives vanish almost everywhere on a level set, without a measurability assumption -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem ae_derivative_zero_on_level (f : ℝ → ℝ) (value : ℝ) :
    ∀ᵐ t ∂volume, f t = value → ∀ d, HasDerivAt f d t → d = 0 := by
  let Z : Set ℝ := {t | f t = value}
  let E : Set ℝ := {t ∈ Z | 𝓝[Z ∩ Ioi t] t = ⊥}
  have hE : E.Countable := countable_setOfPred_isolated_right_within
  have hne : ∀ᵐ t ∂volume, t ∉ E := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hE.measure_zero volume
  filter_upwards [hne] with t ht hft d hd
  have hnb : (𝓝[Z ∩ Ioi t] t).NeBot := ⟨fun h => ht ⟨hft, h⟩⟩
  have hu : UniqueDiffWithinAt ℝ (Z ∩ Ioi t) t := by
    rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin]
    have he : (Z ∩ Ioi t) \ {t} = Z ∩ Ioi t := by
      apply sdiff_eq_left.mpr
      simp only [disjoint_singleton_right, mem_inter_iff, mem_Ioi, lt_self_iff_false,
        and_false, not_false_eq_true]
    rw [he]
    exact hnb
  have hz : HasDerivWithinAt f 0 (Z ∩ Ioi t) t :=
    (hasDerivWithinAt_const t (Z ∩ Ioi t) value).congr (fun _ h => h.1) hft
  exact hu.eq_deriv _ hd.hasDerivWithinAt hz

end Rhone.Statistics.Identifiability
