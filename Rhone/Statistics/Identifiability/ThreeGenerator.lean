/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.Generator
public import Rhone.Statistics.Identifiability.FirstExitLaw

/-!
# First merger among three same-deme island samples

Source: grusea_etal2019, sec. 3.1. -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

abbrev ThreeState := Fin 3

def threeShape : ThreeState → MarkovChain.Identifiability.Shape :=
    ![[[1,1,1]], [[1],[1,1]], [[1],[1],[1]]]

def threeRateCount
    (events : MarkovChain.Identifiability.Shape → List MarkovChain.Identifiability.Shape)
    (i j : ThreeState) : Int :=
  ((events (threeShape i)).countP (fun s => s == threeShape j) : Int) -
    if i = j then (events (threeShape i)).length else 0

theorem three_events_checked :
    (∀ i j, threeRateCount MarkovChain.Identifiability.occupiedEvents i j =
      (![![0,0,0], ![1,-1,0], ![0,6,-6]] : Matrix ThreeState ThreeState Int) i j) ∧
    (∀ i j, threeRateCount MarkovChain.Identifiability.emptyEvents i j =
      (![![-3,3,0], ![0,-2,2], ![0,0,0]] : Matrix ThreeState ThreeState Int) i j) ∧
    (∀ i, MarkovChain.Identifiability.killedCount (threeShape i) = (![3,1,0] : ThreeState → Nat)
        i) := by
  decide

noncomputable def threeGenerator (k : Nat) (c q : ℝ) : Matrix ThreeState ThreeState ℝ :=
  ![![-3*c-3*MarkovChain.Identifiability.totalMigration k
      q,3*MarkovChain.Identifiability.totalMigration k q,0],
    ![q,-c-(2*k+1)*q,2*k*q], ![0,6*q,-6*q]]

theorem threeGenerator_event_formula (k : Nat) (c q : ℝ) (i j : ThreeState) :
    threeGenerator k c q i j =
      (if i = j then -c * (MarkovChain.Identifiability.killedCount (threeShape i) : ℝ) else 0) +
      q * (threeRateCount MarkovChain.Identifiability.occupiedEvents i j : ℝ) +
      q * ((k + 2 - (threeShape i).length : Nat) : ℝ) *
          (threeRateCount MarkovChain.Identifiability.emptyEvents i j : ℝ) := by
  have h1 : k+2-1 = k+1 := by omega
  have h2 : k+2-2 = k := by omega
  rw [three_events_checked.1, three_events_checked.2.1, three_events_checked.2.2]
  fin_cases i <;> fin_cases j <;>
    norm_num [threeGenerator, threeShape, MarkovChain.Identifiability.totalMigration, h1,h2] <;>
        ring

theorem threeGenerator_metzler (k : Nat) (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    IsMetzler (threeGenerator k c q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num
      [threeGenerator, MarkovChain.Identifiability.totalMigration] at * <;> positivity

theorem threeGenerator_row_sum (k : Nat) (c q : ℝ) :
    threeGenerator k c q *ᵥ (fun _ => 1) = ![-3*c,-c,0] := by
  ext i
  fin_cases i <;> simp [threeGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem threeGenerator_rows_nonpos (k : Nat) {c q : ℝ} (hc : 0 ≤ c) (i : ThreeState) :
    (∑ j, threeGenerator k c q i j) ≤ 0 := by
  have h := congrFun (threeGenerator_row_sum k c q) i
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [h]
  fin_cases i <;> simp <;> linarith

noncomputable def threeLyapunov (k : Nat) (c q : ℝ) : ThreeState → ℝ :=
  ![1+(k+2)/c, 1+(k+2)/c+1/(3*q), 1+(k+2)/c+1/(2*q)]

theorem threeLyapunov_ge_one (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ i, 1 ≤ threeLyapunov k c q i := by
  have h : 0 ≤ (k+2 : ℝ)/c := by positivity
  have h3 : 0 ≤ 1/(3*q) := by positivity
  have h2 : 0 ≤ 1/(2*q) := by positivity
  intro i
  fin_cases i <;> dsimp [threeLyapunov] <;> linarith

set_option backward.isDefEq.respectTransparency false in
theorem threeLyapunov_drift (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    threeGenerator k c q *ᵥ threeLyapunov k c q =
      ![-3*c-2*(k+2)-1, -c-(2*k+7)/3-c/(3*q), -1] := by
  ext i
  fin_cases i <;>
    simp [threeGenerator, threeLyapunov, MarkovChain.Identifiability.totalMigration, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> field_simp [hc,hq] <;> ring

theorem three_survival_tendsto_zero (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (i : ThreeState) :
    Filter.Tendsto (flowOutput (threeGenerator k c q) i (fun _ => 1) 0)
      Filter.atTop (nhds 0) := by
  apply survival_tendsto_zero_of_lyapunov _ (threeGenerator_metzler k c hq.le)
    (threeLyapunov k c q) (threeLyapunov_ge_one k hc hq) zero_lt_one
  intro j
  rw [threeLyapunov_drift k hc.ne' hq.ne']
  fin_cases j
  · change -3*c-2*(k+2)-1 ≤ -(1 : ℝ)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · change -c-(2*k+7)/3-c/(3*q) ≤ -(1 : ℝ)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hdiv : 0 ≤ c/(3*q) := by positivity
    linarith
  · exact le_refl _

theorem three_firstExitLaw_probability (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    MeasureTheory.IsProbabilityMeasure (firstExitLaw (threeGenerator k c q) 0) := by
  apply firstExitLaw_probability _ (threeGenerator_metzler k c hq.le) _ 0
    (three_survival_tendsto_zero k hc hq 0)
  intro i
  have h := congrFun (threeGenerator_row_sum k c q) i
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [h]
  fin_cases i <;> simp <;> linarith

end Rhone.Statistics.Identifiability
