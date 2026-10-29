/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairTimes
public import Rhone.Coalescent.IslandPairReach
public import Rhone.MarkovChain.JumpHold

/-! # Labelled island pair hitting-time expectations -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset MeasureTheory

instance stateMeasurableSpace (d : Nat) : MeasurableSpace (State d) := ⊤

instance stateDiscreteMeasurableSpace (d : Nat) : DiscreteMeasurableSpace (State d) :=
  ⟨fun _ => trivial⟩

theorem meanTime_eq_expectedTime (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) :
    meanTime d m c = (chain d m c hm.le hc.le).expectedTime {none} := by
  have hq : ∀ s : State d, s ∉ ({none} : Finset (State d)) →
      (chain d m c hm.le hc.le).rate s ≠ 0 := by
    intro s hs
    cases s with
    | none => simp at hs
    | some p =>
      rcases p with ⟨a,b⟩
      exact ne_of_gt (rate_some_pos d hd m c hm hc a b)
  have h0 : ∀ s ∈ ({none} : Finset (State d)), meanTime d m c s = 0 := by
    intro s hs
    have hs0 : s = none := mem_singleton.mp hs
    subst s
    rfl
  have hgen : ∀ s : State d, s ∉ ({none} : Finset (State d)) →
      ∑ t, (chain d m c hm.le hc.le).Q s t * meanTime d m c t = -(1 : Real) := by
    intro s hs
    cases s with
    | none => simp at hs
    | some p =>
      rcases p with ⟨a,b⟩
      exact meanTime_generator d hd m c hm hc a b
  exact Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (absorbing_set d m c hm.le hc.le) (reaches d hd m c hm hc) hq h0 hgen

theorem expectedTime_same (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a : Fin d) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,a)) = d / c := by
  rw [← meanTime_eq_expectedTime d hd m c hm hc]
  simp [meanTime, sameTime]

theorem expectedTime_different (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) (hab : a ≠ b) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,b)) =
      d / c + (d - 1 : Nat) / (2 * m) := by
  rw [← meanTime_eq_expectedTime d hd m c hm hc]
  simp [meanTime, sameTime, differentTime, hab]

theorem lintegral_timeBefore (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (s : State d) :
    ∫⁻ p, (chain d m c hm.le hc.le).timeBefore {none} p
      ∂(chain d m c hm.le hc.le).jumpHoldLaw s = ENNReal.ofReal (meanTime d m c s) := by
  rw [Rhone.MarkovChain.RateChain.lintegral_timeBefore
    (absorbing_set d m c hm.le hc.le) (reaches d hd m c hm hc)]
  rw [← meanTime_eq_expectedTime d hd m c hm hc]

end Rhone.Coalescent.IslandPair
