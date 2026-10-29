/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.EventKernel
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-! # Event-checked lineage-size chain for five panmictic samples -/

@[expose] public section

open scoped Matrix
namespace Rhone.Statistics.Identifiability

abbrev PanFiveState := Fin 6

def panFiveShape : PanFiveState → List Nat :=
  ![[1,1,1,1,1], [1,1,1,2], [1,1,3], [1,2,2], [1,4], [2,3]]

def panFiveCoalEvents (s : List Nat) : List (List Nat) :=
  (List.range s.length).flatMap (fun i => (List.range i).map (fun j =>
    MarkovChain.Identifiability.sortNat ((s.getD i 0 + s.getD j 0) :: (s.eraseIdx i).eraseIdx j)))

def panFiveGeneratorInt : Matrix PanFiveState PanFiveState Int :=
  ![![-10,10,0,0,0,0], ![0,-6,3,3,0,0], ![0,0,-3,0,2,1],
    ![0,0,0,-3,1,2], ![0,0,0,0,-1,0], ![0,0,0,0,0,-1]]

theorem panFive_events_checked : ∀ i j : PanFiveState,
    ((panFiveCoalEvents (panFiveShape i)).countP (fun s => s == panFiveShape j) : Int) -
      (if i = j then (panFiveCoalEvents (panFiveShape i)).length else 0 : Nat) =
      panFiveGeneratorInt i j := by
  intro i
  fin_cases i <;> decide

theorem panFive_shapes_closed : ∀ i : PanFiveState,
    (panFiveCoalEvents (panFiveShape i)).all
      (fun s => s.length == 1 || (List.ofFn panFiveShape).contains s) = true := by
  decide

noncomputable def panFiveGenerator (rate : ℝ) : Matrix PanFiveState PanFiveState ℝ :=
  fun i j => rate * (panFiveGeneratorInt i j : ℝ)

noncomputable def panFiveReward (w : Nat) (p : PanFiveState → ℝ) : ℝ :=
  ∑ i, p i * ((panFiveShape i).count w : ℝ)

theorem panFive_three_state_difference (rate : ℝ) (p : PanFiveState → ℝ) :
    (∑ j, p j * panFiveGenerator rate j 2) - (∑ j, p j * panFiveGenerator rate j 3) =
      -3*rate*(p 2-p 3) := by
  simp [panFiveGenerator, panFiveGeneratorInt, Fin.sum_univ_succ]
  ring

theorem panFive_two_state_difference (rate : ℝ) (p : PanFiveState → ℝ) :
    (∑ j, p j * panFiveGenerator rate j 4) - (∑ j, p j * panFiveGenerator rate j 5) =
      rate*(p 2-p 3) - rate*(p 4-p 5) := by
  simp [panFiveGenerator, panFiveGeneratorInt, Fin.sum_univ_succ]
  ring

theorem panFive_reward_tail (p : PanFiveState → ℝ) :
    panFiveReward 3 p - panFiveReward 4 p = p 2 - p 4 + p 5 := by
  simp [panFiveReward, panFiveShape, Fin.sum_univ_succ]
  ring

end Rhone.Statistics.Identifiability
