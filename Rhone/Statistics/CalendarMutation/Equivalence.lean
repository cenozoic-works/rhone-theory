/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Equivalence

/-! # Common cumulative calendar clock and collapsed mutation-time object -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.CalendarMutation
open CollapsedGenealogy ThreeTipSites ThreeSiteSeparator

def clockDurations (C : ℝ → ℝ) (g : Joint) : Joint :=
  ((C g.1.1, C (g.1.1 + g.1.2) - C g.1.1), g.2)

def calendarLaw {K L : ℕ} (hK : 0 < K) (C : ℝ → ℝ) (μ : Measure Joint) :
    Measure (Panel K L) :=
  jointSequenceLaw (uniformBlockRoots K L hK) 1 (Measure.map (clockDurations C) μ)

def calendarObject (C : ℝ → ℝ) (μ : Measure Joint) : Measure Joint :=
  object 1 (Measure.map (clockDurations C) μ)

theorem clock_durations_measurable {C : ℝ → ℝ} (hC : Monotone C) :
    Measurable (clockDurations C) := by
  have hm := hC.measurable
  unfold clockDurations
  fun_prop

theorem clock_durations_nonnegative {C : ℝ → ℝ} (hC : Monotone C) (h0 : C 0 = 0)
    (μ : Measure Joint) (hμ : NonnegativeJoint μ) :
    NonnegativeJoint (Measure.map (clockDurations C) μ) := by
  apply (ae_map_iff (clock_durations_measurable hC).aemeasurable (by measurability)).mpr
  filter_upwards [hμ] with g hg
  constructor
  · change 0 ≤ C g.1.1
    rw [← h0]
    exact hC hg.1
  · exact sub_nonneg.mpr (hC (le_add_of_nonneg_right hg.2))

theorem all_calendar_blocks_iff_object_eq {K : ℕ} (hK : 2 ≤ K)
    {C D : ℝ → ℝ} (hC : Monotone C) (hC0 : C 0 = 0)
    (hD : Monotone D) (hD0 : D 0 = 0) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν) :
    (∀ L : ℕ, calendarLaw (L := L) (by omega : 0 < K) C μ =
      calendarLaw (L := L) (by omega : 0 < K) D ν) ↔ calendarObject C μ = calendarObject D ν :=
  all_blocks_iff_collapsed_joint_eq hK (by norm_num) (by norm_num) _ _
    (clock_durations_nonnegative hC hC0 μ hμ) (clock_durations_nonnegative hD hD0 ν hν)

end Rhone.Statistics.CalendarMutation
