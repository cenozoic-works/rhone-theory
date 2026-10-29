/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.Generator
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic

/-! # Global operator-norm bounds for the island generators -/

@[expose] public section

open scoped NNReal Matrix Matrix.Norms.Operator
open Finset

namespace Rhone.Statistics.Identifiability

theorem linfty_opNorm_le_of_abs_row_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ bound) : ‖A‖ ≤ bound := by
  have h : ‖A‖₊ ≤ NNReal.mk bound hbound := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using hrow i
  exact_mod_cast h

theorem coalescenceTable_abs_row_le :
    ∀ i : MarkovChain.Identifiability.State,
        (∑ j, |MarkovChain.Identifiability.coalescenceTable i j|) ≤ 12 := by
  intro i
  fin_cases i <;> decide

theorem recombinationTable_abs_row_le :
    ∀ i : MarkovChain.Identifiability.State,
        (∑ j, |MarkovChain.Identifiability.recombinationTable i j|) ≤ 4 := by
  intro i
  fin_cases i <;> decide

theorem migrationTables_abs_row_le (k : Nat) : ∀ i : MarkovChain.Identifiability.State,
    (∑ j, |MarkovChain.Identifiability.occupiedTable i j|) +
        ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : Int) *
      (∑ j, |MarkovChain.Identifiability.emptyTable i j|) ≤ 8 * ((k : Int) + 3) := by
  intro i
  fin_cases i <;>
    norm_num [MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable,
        MarkovChain.Identifiability.occupiedDemes, Fin.sum_univ_succ] <;> omega

theorem generator_abs_row_le (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (i : MarkovChain.Identifiability.State) :
    (∑ j, |MarkovChain.Identifiability.generator k c q r i j|) ≤ 12*c + 4*r + 8*((k : ℝ)+3)*q := by
  have hC : (∑ j, |(MarkovChain.Identifiability.coalescenceTable i j : ℝ)|) ≤ 12 := by
    exact_mod_cast coalescenceTable_abs_row_le i
  have hR : (∑ j, |(MarkovChain.Identifiability.recombinationTable i j : ℝ)|) ≤ 4 := by
    exact_mod_cast recombinationTable_abs_row_le i
  have hM : (∑ j, |(MarkovChain.Identifiability.occupiedTable i j : ℝ)|) +
      ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) *
        (∑ j, |(MarkovChain.Identifiability.emptyTable i j : ℝ)|) ≤ 8*((k : ℝ)+3) := by
    exact_mod_cast migrationTables_abs_row_le k i
  have hentry (j : MarkovChain.Identifiability.State) : |MarkovChain.Identifiability.generator k c q
      r i j| ≤
      c * |(MarkovChain.Identifiability.coalescenceTable i j : ℝ)| + r *
          |(MarkovChain.Identifiability.recombinationTable i j : ℝ)| +
      q * (|(MarkovChain.Identifiability.occupiedTable i j : ℝ)| +
        ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) *
            |(MarkovChain.Identifiability.emptyTable i j : ℝ)|) := by
    have htriangle (w x y z : ℝ) : |w+x+y+z| ≤ |w|+|x|+|y|+|z| := by
      linarith only [abs_add_le (w+x+y) z, abs_add_le (w+x) y, abs_add_le w x]
    calc
      |MarkovChain.Identifiability.generator k c q r i j| ≤
          |c * (MarkovChain.Identifiability.coalescenceTable i j : ℝ)| + |r *
              (MarkovChain.Identifiability.recombinationTable i j : ℝ)| +
          |q * (MarkovChain.Identifiability.occupiedTable i j : ℝ)| +
          |q * ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) *
              (MarkovChain.Identifiability.emptyTable i j : ℝ)| :=
        htriangle _ _ _ _
      _ = _ := by
        have hm : (0 : ℝ) ≤ ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) :=
            Nat.cast_nonneg _
        simp only [abs_mul, abs_of_nonneg hc, abs_of_nonneg hr, abs_of_nonneg hq,
          abs_of_nonneg hm]
        ring
  calc
    (∑ j, |MarkovChain.Identifiability.generator k c q r i j|) ≤
        ∑ j, (c * |(MarkovChain.Identifiability.coalescenceTable i j : ℝ)| +
          r * |(MarkovChain.Identifiability.recombinationTable i j : ℝ)| +
          q * (|(MarkovChain.Identifiability.occupiedTable i j : ℝ)| +
            ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) *
                |(MarkovChain.Identifiability.emptyTable i j : ℝ)|)) :=
      Finset.sum_le_sum (fun j _ => hentry j)
    _ = c * (∑ j, |(MarkovChain.Identifiability.coalescenceTable i j : ℝ)|) +
        r * (∑ j, |(MarkovChain.Identifiability.recombinationTable i j : ℝ)|) +
        q * ((∑ j, |(MarkovChain.Identifiability.occupiedTable i j : ℝ)|) +
          ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) *
            (∑ j, |(MarkovChain.Identifiability.emptyTable i j : ℝ)|)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ c*12 + r*4 + q*(8*((k : ℝ)+3)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hC hc)
        (mul_le_mul_of_nonneg_left hR hr)) (mul_le_mul_of_nonneg_left hM hq)
    _ = _ := by ring

theorem generator_opNorm_le (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ‖MarkovChain.Identifiability.generator k c q r‖ ≤ 12*c + 4*r + 8*((k : ℝ)+3)*q := by
  apply linfty_opNorm_le_of_abs_row_le _ (by positivity)
  exact generator_abs_row_le k hc hq hr

theorem pairGenerator_opNorm_le_sharp (k : Nat) {c q : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) :
    ‖MarkovChain.Identifiability.pairGenerator k c q‖ ≤ c + 4*((k : ℝ)+1)*q := by
  have hM : 0 ≤ MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  apply linfty_opNorm_le_of_abs_row_le _ (by positivity)
  intro i
  fin_cases i
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change |-c - 2 * MarkovChain.Identifiability.totalMigration k q| + |2 *
        MarkovChain.Identifiability.totalMigration k q| ≤
      c + 4*((k : ℝ)+1)*q
    rw [abs_of_nonpos
        (show -c - 2 * MarkovChain.Identifiability.totalMigration k q ≤ 0 by linarith),
      abs_of_nonneg (show 0 ≤ 2 * MarkovChain.Identifiability.totalMigration k q by positivity)]
    unfold MarkovChain.Identifiability.totalMigration
    ring_nf
    exact le_rfl
  · simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_succ, abs_mul, abs_of_nonneg hq]
    nlinarith only [hc, mul_nonneg (Nat.cast_nonneg k) hq]

theorem pairGenerator_opNorm_le (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ‖MarkovChain.Identifiability.pairGenerator k c q‖ ≤ 12*c + 4*r + 8*((k : ℝ)+3)*q := by
  calc
    ‖MarkovChain.Identifiability.pairGenerator k c q‖ ≤ c + 4*((k : ℝ)+1)*q :=
        pairGenerator_opNorm_le_sharp k hc hq
    _ ≤ _ := by nlinarith only [hc, hq, hr, mul_nonneg (Nat.cast_nonneg k) hq]

end Rhone.Statistics.Identifiability
