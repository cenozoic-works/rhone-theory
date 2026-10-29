/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.Category

/-! # Exact multiplicities for the five equality categories -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.ConcretePatternMoments
open ThreeTipSites

def multiplicityNat (i : Fin 5) : ℕ := ![4, 12, 12, 12, 24] i

def multiplicity (i : Fin 5) : ℝ := multiplicityNat i

theorem category_fiber_card (i : Fin 5) :
    (Finset.univ.filter (fun x : Triple 4 => category x = i)).card = multiplicityNat i := by
  fin_cases i <;> decide

theorem category_sum (f : Fin 5 → ℝ) :
    (∑ x : Triple 4, f (category x)) = ∑ i : Fin 5, multiplicity i * f i := by
  rw [← Finset.sum_fiberwise' Finset.univ category f]
  simp only [Finset.sum_const, category_fiber_card, nsmul_eq_mul, multiplicity]

def panelTuple : Panel 4 3 ≃ (Triple 4 × Triple 4 × Triple 4) where
  toFun x := (x 0, x 1, x 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv := by intro x; funext i; fin_cases i <;> rfl
  right_inv := by intro x; rfl

theorem category_panel_sum (f : Row → ℝ) :
    (∑ x : Panel 4 3, f (rowOf x)) =
      ∑ r : Row, multiplicity r.1 * multiplicity r.2.1 * multiplicity r.2.2 * f r := by
  rw [← panelTuple.symm.sum_comp (fun x => f (rowOf x))]
  change (∑ x : Triple 4 × Triple 4 × Triple 4,
    f (category x.1, category x.2.1, category x.2.2)) = _
  rw [Fintype.sum_prod_type]
  conv_lhs => arg 2; ext a; rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]; arg 2; ext a; rw [Fintype.sum_prod_type]
  rw [category_sum (fun i => ∑ b : Triple 4, ∑ c : Triple 4, f (i, category b, category c))]
  have hb (i : Fin 5) : (∑ b : Triple 4, ∑ c : Triple 4, f (i, category b, category c)) =
      ∑ j : Fin 5, multiplicity j * ∑ c : Triple 4, f (i, j, category c) :=
    category_sum (fun j => ∑ c : Triple 4, f (i, j, category c))
  have hc (i j : Fin 5) : (∑ c : Triple 4, f (i, j, category c)) =
      ∑ k : Fin 5, multiplicity k * f (i, j, k) := category_sum (fun k => f (i, j, k))
  simp_rw [hb, hc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

end Rhone.Statistics.ConcretePatternMoments
