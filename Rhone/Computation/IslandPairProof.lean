/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.IslandPair
public import Rhone.Coalescent.IslandPairExpected

/-! # Supplied rational island times equal the labelled hitting times -/

@[expose] public section
namespace Rhone.Computation.IslandPair

theorem sameTime_cast (d : Nat) (c : Rat) :
    (sameTime d c : Real) = Rhone.Coalescent.IslandPair.sameTime d (c : Real) := by
  simp [sameTime, Rhone.Coalescent.IslandPair.sameTime]

theorem differentTime_cast (d : Nat) (m c : Rat) :
    (differentTime d m c : Real) = Rhone.Coalescent.IslandPair.differentTime d m c := by
  simp [differentTime, sameTime_cast, Rhone.Coalescent.IslandPair.differentTime]

theorem sameTime_eq_expectedTime (d : Nat) (hd : 2 ≤ d) (m c : Rat)
    (hm : 0 < (m : Real)) (hc : 0 < (c : Real)) (a : Fin d) :
    (sameTime d c : Real) =
      (Rhone.Coalescent.IslandPair.chain d m c hm.le hc.le).expectedTime {none} (some (a,a)) := by
  rw [Rhone.Coalescent.IslandPair.expectedTime_same d hd m c hm hc]
  simp [sameTime]

theorem differentTime_eq_expectedTime (d : Nat) (hd : 2 ≤ d) (m c : Rat)
    (hm : 0 < (m : Real)) (hc : 0 < (c : Real)) (a b : Fin d) (hab : a ≠ b) :
    (differentTime d m c : Real) =
      (Rhone.Coalescent.IslandPair.chain d m c hm.le hc.le).expectedTime {none} (some (a,b)) := by
  rw [Rhone.Coalescent.IslandPair.expectedTime_different d hd m c hm hc a b hab]
  simp [differentTime, sameTime]

theorem timeContrast_eq (d : Nat) (hd : 2 ≤ d) (m c : Rat) (hm : 0 < m) (hc : 0 < c) :
    timeContrast d m c = (differentTime d m c - sameTime d c) / differentTime d m c := by
  have hn : ((d - 1 : Nat) : Rat) = (d : Rat) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hdq : (0 : Rat) < d := Nat.cast_pos.mpr (by omega)
  have hden : (0 : Rat) < 2 * d * m + c * (d - 1 : Nat) := by positivity
  unfold timeContrast differentTime sameTime
  rw [hn] at *
  field_simp [ne_of_gt hm, ne_of_gt hc, ne_of_gt hden]; ring

theorem check_iff (d : Nat) (m c : Rat) (claim : Array Rat) :
    check d m c claim = true ↔ claim = values d m c := by simp [check]

theorem check_complete (d : Nat) (m c : Rat) : check d m c (values d m c) = true := by
  simp [check]

end Rhone.Computation.IslandPair
