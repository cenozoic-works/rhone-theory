/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingFirstExit

/-! # Locus exchange for the time-dependent pre-first-event evolution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

def locusExchangeState : MarkovChain.Identifiability.State → MarkovChain.Identifiability.State :=
  ![0, 1, 2, 5, 4, 3, 6, 7, 10, 9, 8, 11, 14, 13, 12, 15]

theorem locusExchangeState_involutive : Function.Involutive locusExchangeState := by
  intro i
  fin_cases i <;> decide

def locusExchangeEquiv : MarkovChain.Identifiability.State ≃ MarkovChain.Identifiability.State :=
  { toFun := locusExchangeState
    invFun := locusExchangeState
    left_inv := locusExchangeState_involutive
    right_inv := locusExchangeState_involutive }

@[simp] theorem locusExchangeState_zero : locusExchangeState 0 = 0 := rfl

theorem locusExchangeState_shape (i : MarkovChain.Identifiability.State) :
    MarkovChain.Identifiability.shape (locusExchangeState i) =
      MarkovChain.Identifiability.canonical
          ((MarkovChain.Identifiability.shape i).map
          (List.map (fun a => if a = 1 then 2 else if a = 2 then 1 else a)))
        := by
  fin_cases i <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem locusExchangeState_tables :
    (∀ i j, MarkovChain.Identifiability.coalescenceTable (locusExchangeState i)
        (locusExchangeState j) = MarkovChain.Identifiability.coalescenceTable i j) ∧
    (∀ i j, MarkovChain.Identifiability.recombinationTable (locusExchangeState i)
        (locusExchangeState j) = MarkovChain.Identifiability.recombinationTable
      i j) ∧
    (∀ i j, MarkovChain.Identifiability.occupiedTable (locusExchangeState i)
        (locusExchangeState j) = MarkovChain.Identifiability.occupiedTable i j) ∧
    (∀ i j, MarkovChain.Identifiability.emptyTable (locusExchangeState i) (locusExchangeState j) =
        MarkovChain.Identifiability.emptyTable i j) ∧
    (∀ i, MarkovChain.Identifiability.occupiedDemes (locusExchangeState i) =
        MarkovChain.Identifiability.occupiedDemes i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals intro i; fin_cases i <;> decide

theorem locusExchangeState_markCounts (i : MarkovChain.Identifiability.State) :
    markCount (locusExchangeState i) 1 = markCount i 3 ∧
    markCount (locusExchangeState i) 2 = markCount i 4 := by
  fin_cases i <;> decide

theorem generator_locusExchange (k : ℕ) (c q r : ℝ) (i j : MarkovChain.Identifiability.State) :
    MarkovChain.Identifiability.generator k c q r (locusExchangeState i) (locusExchangeState j) =
      MarkovChain.Identifiability.generator k c q r i j := by
  rcases locusExchangeState_tables with ⟨hc, hr, hq, he, ho⟩
  simp only [MarkovChain.Identifiability.generator, hc, hr, hq, he, ho]

theorem inhomogeneousRowOperator_locusExchange (k : ℕ) (c q r : ℝ)
    (x : MarkovChain.Identifiability.State → ℝ) (hx : ∀ i, x (locusExchangeState i) = x i)
        (j : MarkovChain.Identifiability.State) :
    inhomogeneousRowOperator (MarkovChain.Identifiability.generator k c q r) x
        (locusExchangeState j) =
      inhomogeneousRowOperator (MarkovChain.Identifiability.generator k c q r) x j := by
  change (∑ i, x i * MarkovChain.Identifiability.generator k c q r i (locusExchangeState j)) =
    ∑ i, x i * MarkovChain.Identifiability.generator k c q r i j
  rw [← locusExchangeEquiv.sum_comp
      (fun i => x i * MarkovChain.Identifiability.generator k c q r i (locusExchangeState j))]
  change (∑ i, x (locusExchangeState i) *
    MarkovChain.Identifiability.generator k c q r (locusExchangeState i) (locusExchangeState j)) = _
  simp only [hx, generator_locusExchange]

theorem preTerm_locusExchange (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (n : ℕ) (t : ℝ)
        (j : MarkovChain.Identifiability.State) :
    PeanoBaker.term (fun s => inhomogeneousRowOperator (timeVaryingARGGenerator k c q r s))
      ((1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ) 0) n t
          (locusExchangeState j) =
    PeanoBaker.term (fun s => inhomogeneousRowOperator (timeVaryingARGGenerator k c q r s))
      ((1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ) 0) n t
          j := by
  let A := fun s => inhomogeneousRowOperator (timeVaryingARGGenerator k c q r s)
  let x := ((1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ) 0)
  have hA : Continuous A := inhomogeneousRowOperator_continuous _
    (timeVaryingARGGenerator_continuous k c q r hc hq hr)
  change PeanoBaker.term A x n t (locusExchangeState j) = PeanoBaker.term A x n t j
  induction n generalizing t j with
  | zero =>
    fin_cases j <;> rfl
  | succ n ih =>
    have hcont : Continuous (fun s => A s (PeanoBaker.term A x n s)) :=
      hA.clm_apply (PeanoBaker.term_continuous A hA x n)
    have hi : IntervalIntegrable (fun s => A s (PeanoBaker.term A x n s)) volume 0 t :=
      hcont.intervalIntegrable 0 t
    rw [PeanoBaker.term_succ]
    change (ContinuousLinearMap.proj (locusExchangeState j) :
        (MarkovChain.Identifiability.State → ℝ) →L[ℝ] ℝ)
      (∫ s in (0 : ℝ)..t, A s (PeanoBaker.term A x n s)) =
      (ContinuousLinearMap.proj j : (MarkovChain.Identifiability.State → ℝ) →L[ℝ] ℝ)
      (∫ s in (0 : ℝ)..t, A s (PeanoBaker.term A x n s))
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hi,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
    apply intervalIntegral.integral_congr
    intro s _
    exact inhomogeneousRowOperator_locusExchange k (c s) (q s) (r s)
      (PeanoBaker.term A x n s) (fun i => ih s i) j

theorem timeVaryingPreRow_locusExchange (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ)
        (i : MarkovChain.Identifiability.State) :
    timeVaryingPreRow k c q r t (locusExchangeState i) =
      timeVaryingPreRow k c q r t i := by
  have hQ := timeVaryingARGGenerator_continuous k c q r hc hq hr
  simp only [timeVaryingPreRow, inhomogeneousTransition,
    inhomogeneousFundamentalInverse_zero _ hQ, Matrix.one_mul,
    inhomogeneousFundamental, PeanoBaker.solution]
  have hs := PeanoBaker.term_summable
    (fun s => inhomogeneousRowOperator (timeVaryingARGGenerator k c q r s))
    (inhomogeneousRowOperator_continuous _ hQ)
        ((1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ) 0) t
  rw [Pi.tsum_apply hs, Pi.tsum_apply hs]
  exact tsum_congr fun n => preTerm_locusExchange k c q r hc hq hr n t i

theorem timeVaryingMarkFlux_locusExchange_same (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingMarkFlux k c q r 1 t = timeVaryingMarkFlux k c q r 3 t := by
  unfold timeVaryingMarkFlux
  rw [← locusExchangeEquiv.sum_comp (fun i =>
    timeVaryingPreRow k c q r t i * markRates (c t) i 1)]
  apply Finset.sum_congr rfl
  intro i _
  change timeVaryingPreRow k c q r t (locusExchangeState i) *
    (c t * (markCount (locusExchangeState i) 1 : ℝ)) = _
  rw [timeVaryingPreRow_locusExchange k c q r hc hq hr,
    (locusExchangeState_markCounts i).1]
  rfl

theorem timeVaryingMarkFlux_locusExchange_apart (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingMarkFlux k c q r 2 t = timeVaryingMarkFlux k c q r 4 t := by
  unfold timeVaryingMarkFlux
  rw [← locusExchangeEquiv.sum_comp (fun i =>
    timeVaryingPreRow k c q r t i * markRates (c t) i 2)]
  apply Finset.sum_congr rfl
  intro i _
  change timeVaryingPreRow k c q r t (locusExchangeState i) *
    (c t * (markCount (locusExchangeState i) 2 : ℝ)) = _
  rw [timeVaryingPreRow_locusExchange k c q r hc hq hr,
    (locusExchangeState_markCounts i).2]
  rfl

end Rhone.Statistics.Identifiability
