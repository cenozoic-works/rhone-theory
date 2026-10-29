/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependenceBudget.Transfer
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Finite iid experiments for the paired tests -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

noncomputable def iid (P : Law X) (N : ℕ) : Law (Fin N → X) where
  mass := fun x => ∏ i, P.mass (x i)
  nonneg := fun x => Finset.prod_nonneg (fun i _ => P.nonneg (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

theorem expectation_product (P : Law X) (N : ℕ) (f : Fin N → X → ℝ) :
    rejection (iid P N) (fun x => ∏ i, f i (x i)) = ∏ i, rejection P (f i) := by
  simp only [rejection, iid, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => P.mass x * f i x)).symm

theorem expectation_coordinate (P : Law X) (N : ℕ) (f : X → ℝ) (i : Fin N) :
    rejection (iid P N) (fun x => f (x i)) = rejection P f := by
  have h := expectation_product P N (fun j x => if j = i then f x else 1)
  have hh : ∀ j : Fin N, rejection P (fun x => if j = i then f x else 1) =
      if j = i then rejection P f else 1 := by
    intro j
    by_cases hji : j = i <;> simp [hji, rejection, P.total]
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, hh] using h

theorem expectation_two_coordinates (P : Law X) (N : ℕ) (f g : X → ℝ)
    (i j : Fin N) (hij : i ≠ j) :
    rejection (iid P N) (fun x => f (x i) * g (x j)) =
      rejection P f * rejection P g := by
  have h := expectation_product P N
    (fun k x => (if k = i then f x else 1) * (if k = j then g x else 1))
  have hh : ∀ k : Fin N,
      rejection P (fun x => (if k = i then f x else 1) * (if k = j then g x else 1)) =
        (if k = i then rejection P f else 1) * (if k = j then rejection P g else 1) := by
    intro k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [rejection, P.total]
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true, hh]
    using h

end Rhone.Statistics.DependentPairedTest
