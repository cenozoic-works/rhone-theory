/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Denominator.Transfer
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # Transfer tools for allele refinements -/

@[expose] public section

namespace Rhone.Algebra.GenericCoordinates

open Denominator

theorem sharpness_transfer_unit {F : Type*} [Field F] {A : Subring F}
    {x c u Φ Ψ D Dc E d : F}
    (hx : x = c * Φ + Ψ) (hu : u * c = 1) (huA : u ∈ A)
    (hΨ : Clears A Ψ Dc) (hDc : Dc ≠ 0) (hD : D = Dc * E)
    (hH : IsRedDenom A Φ D) (hd : Clears A x d) : DvdIn A E d := by
  have hsplit : u * x = 1 * Φ + u * Ψ := by
    rw [hx, mul_add, ← mul_assoc, hu]
  have hrem : Clears A (u * Ψ) Dc := ⟨hΨ.1, by
    rw [mul_left_comm]
    exact A.mul_mem huA hΨ.2⟩
  have hclear : Clears A (u * x) d := ⟨hd.1, by
    rw [mul_left_comm]
    exact A.mul_mem huA hd.2⟩
  exact dvdIn_of_split_clears hsplit (mul_one 1) A.one_mem hrem hDc hD hH hclear

section Aggregation

open scoped BigOperators

variable {K ι : Type*} [Field K]

theorem denom_sum_dvd_prod (s : Finset ι) (q : ι → RatFunc K) :
    RatFunc.denom (∑ i ∈ s, q i) ∣ ∏ i ∈ s, RatFunc.denom (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RatFunc.denom_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (RatFunc.denom_add_dvd _ _).trans (mul_dvd_mul_left _ ih)

theorem exists_pole_of_aggregate {s : Finset ι} {q : ι → RatFunc K}
    {e : Polynomial K} (he : Prime e)
    (h : e ∣ RatFunc.denom (∑ i ∈ s, q i)) :
    ∃ i ∈ s, e ∣ RatFunc.denom (q i) := by
  classical
  exact (he.dvd_finsetProd_iff (fun i => RatFunc.denom (q i))).mp (h.trans (denom_sum_dvd_prod s q))

theorem exists_pole_of_aggregate_irreducible {s : Finset ι} {q : ι → RatFunc K}
    {e : Polynomial K} (he : Irreducible e)
    (h : e ∣ RatFunc.denom (∑ i ∈ s, q i)) :
    ∃ i ∈ s, e ∣ RatFunc.denom (q i) :=
  exists_pole_of_aggregate he.prime h

end Aggregation

end Rhone.Algebra.GenericCoordinates
