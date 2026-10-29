/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Rhone.Probability.Closure.MatchingGeneratingFunction
public import Std.Data.HashMap.Lemmas
public import Mathlib.Data.List.Basic

/-! # Interpretation of the executable sparse polynomial -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open Probability.Closure

abbrev Key := Nat × Nat × Nat

noncomputable def exponent (key : Key) : Fin 3 →₀ Nat :=
  mono3 key.1 key.2.1 key.2.2

noncomputable def reflectList (terms : List (Key × Rat)) : MvPolynomial (Fin 3) Rat :=
  (terms.map fun term => MvPolynomial.monomial (exponent term.1) term.2).sum

noncomputable def reflect (g : Poly) : MvPolynomial (Fin 3) Rat := reflectList g.toList

def listCoefficient (terms : List (Key × Rat)) (key : Key) : Rat :=
  (terms.map fun term => if term.1 = key then term.2 else 0).sum

theorem exponent_injective : Function.Injective exponent := by
  intro k l h
  obtain ⟨i, j, t⟩ := k
  obtain ⟨a, b, u⟩ := l
  obtain ⟨rfl, rfl, rfl⟩ := mono3_eq_iff.mp h
  rfl

theorem exponent_surjective : Function.Surjective exponent := by
  intro d
  refine ⟨(d 0, d 1, d 2), ?_⟩
  ext i
  fin_cases i <;> simp [exponent]

theorem coeff_reflectList (terms : List (Key × Rat)) (key : Key) :
    (reflectList terms).coeff (exponent key) = listCoefficient terms key := by
  induction terms with
  | nil => simp [reflectList, listCoefficient]
  | cons term terms ih =>
    simp only [reflectList, listCoefficient, List.map_cons, List.sum_cons,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_monomial] at *
    rw [ih]
    by_cases he : term.1 = key
    · simp [he]
    · have hd : exponent term.1 ≠ exponent key := fun h => he (exponent_injective h)
      simp [he, hd]

theorem coeff_reflect (g : Poly) (key : Key) :
    (reflect g).coeff (exponent key) = listCoefficient g.toList key :=
  coeff_reflectList g.toList key

theorem reflect_ext {a b : Poly}
    (h : ∀ key, listCoefficient a.toList key = listCoefficient b.toList key) :
    reflect a = reflect b := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨key, rfl⟩ := exponent_surjective d
  simpa only [coeff_reflect] using h key

end Rhone.Computation.PolynomialEncoding
