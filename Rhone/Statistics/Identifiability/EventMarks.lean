/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GeneratorValid

/-! # Five possible marks at the first overlapping-material merger -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

def aTogether (s : MarkovChain.Identifiability.Shape) : Bool :=
  s.any (fun g => g.countP (fun a => MarkovChain.Identifiability.carriesA a) == 2)

def markCount (i : MarkovChain.Identifiability.State) (m : Fin 5) : Nat :=
  (MarkovChain.Identifiability.mergerEvents (MarkovChain.Identifiability.shape i)).countP (fun e =>
    if m = 0 then e.1 == 3 else
    if m = 1 then e.1 == 1 && MarkovChain.Identifiability.bTogether e.2 else
    if m = 2 then e.1 == 1 && !MarkovChain.Identifiability.bTogether e.2 else
    if m = 3 then e.1 == 2 && aTogether e.2 else
    e.1 == 2 && !aTogether e.2)

theorem mark_partition : ∀ i : MarkovChain.Identifiability.State, (∑ m, markCount i m) =
    MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) := by
  intro i
  fin_cases i <;> decide

theorem mark_A_counts : ∀ i : MarkovChain.Identifiability.State,
    markCount i 1 = MarkovChain.Identifiability.firstAThenBTable i ∧
    markCount i 1 + markCount i 2 = MarkovChain.Identifiability.firstATable i := by
  intro i
  fin_cases i <;> decide

noncomputable def markRates (c : ℝ) : Matrix MarkovChain.Identifiability.State (Fin 5) ℝ :=
  fun i m => c * (markCount i m : ℝ)

theorem markRates_nonneg {c : ℝ} (hc : 0 ≤ c) : ∀ i m, 0 ≤ markRates c i m :=
  fun _ _ => mul_nonneg hc (Nat.cast_nonneg _)

theorem markRates_sum (c : ℝ) (i : MarkovChain.Identifiability.State) :
    (∑ m, markRates c i m) = c *
        (MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) : ℝ) := by
  simp only [markRates, ← Finset.mul_sum, ← Nat.cast_sum, mark_partition]

theorem markRates_A_same (c : ℝ) (i : MarkovChain.Identifiability.State) : markRates c i 1 =
    firstAKernel c i 0 := by
  simp [markRates, firstAKernel, (mark_A_counts i).1]

theorem markRates_A_apart (c : ℝ) (i : MarkovChain.Identifiability.State) : markRates c i 2 =
    firstAKernel c i 1 := by
  have h : (markCount i 1 : ℝ) + (markCount i 2 : ℝ) =
      (MarkovChain.Identifiability.firstATable i : ℝ) := by
    exact_mod_cast (mark_A_counts i).2
  have h1 : (markCount i 1 : ℝ) = (MarkovChain.Identifiability.firstAThenBTable i : ℝ) := by
    exact_mod_cast (mark_A_counts i).1
  change c * (markCount i 2 : ℝ) = c *
      ((MarkovChain.Identifiability.firstATable i : ℝ) -
      (MarkovChain.Identifiability.firstAThenBTable i : ℝ))
  congr 1
  linarith

end Rhone.Statistics.Identifiability
