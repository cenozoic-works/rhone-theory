/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.Generator
public import Rhone.Statistics.Identifiability.CTMC
public import Rhone.Statistics.Identifiability.JointDensity

/-! # Positivity and mass balance of the independently checked event generator -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset
namespace Rhone.Statistics.Identifiability

theorem table_offdiag_nonneg : ∀ i j : MarkovChain.Identifiability.State, i ≠ j →
    0 ≤ MarkovChain.Identifiability.coalescenceTable i j ∧ 0 ≤
        MarkovChain.Identifiability.recombinationTable i j ∧
    0 ≤ MarkovChain.Identifiability.occupiedTable i j ∧ 0 ≤ MarkovChain.Identifiability.emptyTable i
        j := by
  intro i
  fin_cases i <;> decide

theorem table_row_sums : ∀ i : MarkovChain.Identifiability.State,
    (∑ j, MarkovChain.Identifiability.coalescenceTable i j) =
        -(MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) : Int) ∧
    (∑ j, MarkovChain.Identifiability.recombinationTable i j) = 0 ∧
    (∑ j, MarkovChain.Identifiability.occupiedTable i j) = 0 ∧
        (∑ j, MarkovChain.Identifiability.emptyTable i j) = 0 := by
  intro i
  fin_cases i <;> decide

theorem generator_metzler (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) : IsMetzler
        (MarkovChain.Identifiability.generator k c q r) := by
  intro i j hij
  obtain ⟨hC,hR,hO,hE⟩ := table_offdiag_nonneg i j hij
  unfold MarkovChain.Identifiability.generator
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg hc (by exact_mod_cast hC))
    (mul_nonneg hr (by exact_mod_cast hR)))
    (mul_nonneg hq (by exact_mod_cast hO)))
    (mul_nonneg (mul_nonneg hq (Nat.cast_nonneg _)) (by exact_mod_cast hE))

theorem generator_row_sum (k : Nat) (c q r : ℝ) (i : MarkovChain.Identifiability.State) :
    (∑ j, MarkovChain.Identifiability.generator k c q r i j) = -c *
        MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) := by
  obtain ⟨hC,hR,hO,hE⟩ := table_row_sums i
  have hC' : (∑ j, (MarkovChain.Identifiability.coalescenceTable i j : ℝ)) =
      -(MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) : ℝ) := by
    exact_mod_cast hC
  have hR' : (∑ j, (MarkovChain.Identifiability.recombinationTable i j : ℝ)) = 0 :=
      by exact_mod_cast hR
  have hO' : (∑ j, (MarkovChain.Identifiability.occupiedTable i j : ℝ)) = 0 := by exact_mod_cast hO
  have hE' : (∑ j, (MarkovChain.Identifiability.emptyTable i j : ℝ)) = 0 := by exact_mod_cast hE
  simp only [MarkovChain.Identifiability.generator, sum_add_distrib, ← mul_sum, hC', hR', hO', hE']
  ring

theorem firstAKernel_nonneg {c : ℝ} (hc : 0 ≤ c) :
    ∀ i j, 0 ≤ firstAKernel c i j := by
  have h : ∀ i : MarkovChain.Identifiability.State, MarkovChain.Identifiability.firstAThenBTable i ≤
      MarkovChain.Identifiability.firstATable i := by
    intro i
    fin_cases i <;> decide
  intro i j
  unfold firstAKernel
  split
  · exact mul_nonneg hc (Nat.cast_nonneg _)
  · exact mul_nonneg hc (sub_nonneg.mpr (by exact_mod_cast h i))

theorem pairGenerator_metzler (k : Nat) {c q : ℝ} (hq : 0 ≤ q) :
    IsMetzler (MarkovChain.Identifiability.pairGenerator k c q) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change 0 ≤ 2 * ((k + 1 : ℝ) * q)
    positivity
  · change 0 ≤ 2 * q
    positivity
  · exact (hij rfl).elim

end Rhone.Statistics.Identifiability
