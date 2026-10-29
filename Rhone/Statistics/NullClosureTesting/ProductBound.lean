/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProduct
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Finite-product continuity bound for null-closure testing -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.NullClosureTesting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

theorem mass_le_one (P : Law X) (x : X) : P.mass x ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun y _ => P.nonneg y) (Finset.mem_univ x)

theorem atom_difference_le (P Q : Law X) (x : X) :
    |P.mass x - Q.mass x| ≤ 2 * totalVariation P Q := by
  have h := Finset.single_le_sum (fun y (_ : y ∈ Finset.univ) =>
    abs_nonneg (P.mass y - Q.mass y)) (Finset.mem_univ x)
  unfold totalVariation
  linarith

theorem bounded_product_difference {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have has := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hbp : 0 ≤ ∏ j ∈ s, b j := Finset.prod_nonneg fun j hj => (hbs j hj).1
    have hbone : ∏ j ∈ s, b j ≤ 1 := Finset.prod_le_one₀
      (fun j hj => (hbs j hj).1) (fun j hj => (hbs j hj).2)
    have hai := ha i (Finset.mem_insert_self i s)
    calc
      _ = |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
          (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
      _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
          |a i - b i| * |∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le
          (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)) ((a i - b i) * ∏ j ∈ s, b j)
      _ ≤ ∑ j ∈ s, |a j - b j| + |a i - b i| := by
        rw [abs_of_nonneg hai.1, abs_of_nonneg hbp]
        apply add_le_add
        · exact (mul_le_of_le_one_left (abs_nonneg _) hai.2).trans (ih has hbs)
        · exact mul_le_of_le_one_right (abs_nonneg _) hbone
      _ = _ := by ring

end Rhone.Statistics.NullClosureTesting
