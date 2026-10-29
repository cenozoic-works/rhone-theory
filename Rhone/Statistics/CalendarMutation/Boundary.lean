/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CalendarMutation.KnownClock

/-! # Plateau example: positive calendar internal length, invisible label -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.CalendarMutation
open CollapsedGenealogy ThreeSiteSeparator

def plateau (t : ℝ) : ℝ := min t 1

theorem plateau_monotone : Monotone plateau := fun _ _ h => min_le_min h le_rfl

theorem plateau_zero : plateau 0 = 0 := by norm_num [plateau]

theorem plateau_clock_durations (q : Fin 3) : clockDurations plateau ((2, 1), q) = ((1, 0), q) := by
  norm_num [clockDurations, plateau]

theorem distinct_resolved_cherry_measures :
    Measure.dirac (((2, 1), 0) : Joint) ≠ Measure.dirac (((2, 1), 1) : Joint) := by
  intro he
  have hh := congrArg (fun M : Measure Joint => M {(((2, 1), 0) : Joint)}) he
  simp at hh

theorem resolved_cherries_hidden_by_plateau {K L : ℕ} (hK : 0 < K) (q p : Fin 3) :
    calendarLaw (L := L) hK plateau (Measure.dirac (((2, 1), q) : Joint)) =
      calendarLaw (L := L) hK plateau (Measure.dirac (((2, 1), p) : Joint)) := by
  unfold calendarLaw
  rw [Measure.map_dirac' (clock_durations_measurable plateau_monotone) _,
    Measure.map_dirac' (clock_durations_measurable plateau_monotone) _,
    plateau_clock_durations, plateau_clock_durations]
  exact star_labels_same_sequence_law hK 1 1 q p

end Rhone.Statistics.CalendarMutation
