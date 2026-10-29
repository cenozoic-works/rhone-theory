/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CalendarMutation.Equivalence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Recovery of calendar durations and labels for a known strict clock -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.CalendarMutation
open CollapsedGenealogy

theorem clock_durations_injective {C : ℝ → ℝ} (hC : StrictMono C) :
    Function.Injective (clockDurations C) := by
  intro g h he
  have hu := congrArg (fun x : Joint => x.1.1) he
  have hv := congrArg (fun x : Joint => x.1.2) he
  have hq := congrArg (fun x : Joint => x.2) he
  have hu' : g.1.1 = h.1.1 := hC.injective hu
  have hs : g.1.1 + g.1.2 = h.1.1 + h.1.2 := by
    apply hC.injective
    change C (g.1.1 + g.1.2) - C g.1.1 = C (h.1.1 + h.1.2) - C h.1.1 at hv
    rw [hu'] at hv ⊢
    linarith
  exact Prod.ext (Prod.ext hu' (by linarith)) hq

theorem strict_calendar_object {C : ℝ → ℝ} (hC : StrictMono C) (μ : Measure Joint)
    (hv : ∀ᵐ g ∂μ, 0 < g.1.2) :
    calendarObject C μ = Measure.map (clockDurations C) μ := by
  unfold calendarObject object
  rw [Measure.map_map (collapse_measurable.comp (scale_measurable 1))
    (clock_durations_measurable hC.monotone)]
  apply Measure.map_congr
  filter_upwards [hv] with g hg
  have hp : 0 < C (g.1.1 + g.1.2) - C g.1.1 :=
    sub_pos.mpr (hC (lt_add_of_pos_right _ hg))
  simp [Function.comp_apply, collapse, scale, clockDurations, ne_of_gt hp]

theorem all_calendar_blocks_known_clock_iff {K : ℕ} (hK : 2 ≤ K)
    {C : ℝ → ℝ} (hC : StrictMono C) (h0 : C 0 = 0) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν)
    (hvμ : ∀ᵐ g ∂μ, 0 < g.1.2) (hvν : ∀ᵐ g ∂ν, 0 < g.1.2) :
    (∀ L : ℕ, calendarLaw (L := L) (by omega : 0 < K) C μ =
      calendarLaw (L := L) (by omega : 0 < K) C ν) ↔ μ = ν := by
  rw [all_calendar_blocks_iff_object_eq hK hC.monotone h0 hC.monotone h0 μ ν hμ hν,
    strict_calendar_object hC μ hvμ, strict_calendar_object hC ν hvν]
  exact (clock_durations_measurable hC.monotone).measurableEmbedding
    (clock_durations_injective hC) |>.map_injective.eq_iff

end Rhone.Statistics.CalendarMutation
