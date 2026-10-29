/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialHashMapProof

/-! # Sparse multiplication denotes polynomial multiplication -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

private def keyAdd (a b : Key) : Key :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

private def accumulate (m : Std.HashMap Key Rat) (a b : Key × Rat) :
    Std.HashMap Key Rat :=
  let key := keyAdd a.1 b.1
  let v := m.getD key 0 + a.2 * b.2
  if v == 0 then m.erase key else m.insert key v

private theorem exponent_keyAdd (a b : Key) :
    exponent (keyAdd a b) = exponent a + exponent b := by
  ext i
  fin_cases i <;> simp [keyAdd, exponent]

private theorem reflect_accumulate (m : Std.HashMap Key Rat) (a b : Key × Rat) :
    reflect (accumulate m a b).toArray = reflect m.toArray +
      MvPolynomial.monomial (exponent a.1) a.2 *
        MvPolynomial.monomial (exponent b.1) b.2 := by
  unfold accumulate
  rw [reflect_hashMap_update, exponent_keyAdd, MvPolynomial.monomial_mul_monomial]

private theorem reflect_inner (terms : List (Key × Rat)) (m : Std.HashMap Key Rat)
    (a : Key × Rat) :
    reflect (terms.foldl (fun m b => accumulate m a b) m).toArray =
      reflect m.toArray + MvPolynomial.monomial (exponent a.1) a.2 * reflectList terms := by
  induction terms generalizing m with
  | nil => simp [reflectList]
  | cons b terms ih =>
    rw [List.foldl_cons, ih, reflect_accumulate]
    simp [reflectList, mul_add, add_assoc]

private theorem reflect_outer (a b : List (Key × Rat)) (m : Std.HashMap Key Rat) :
    reflect (a.foldl (fun m x => b.foldl (fun m y => accumulate m x y) m) m).toArray =
      reflect m.toArray + reflectList a * reflectList b := by
  induction a generalizing m with
  | nil => simp [reflectList]
  | cons x a ih =>
    rw [List.foldl_cons, ih, reflect_inner]
    simp [reflectList, add_mul, add_assoc]

private theorem mulPoly_eq_fold (a b : Poly) :
    mulPoly a b = (a.toList.foldl (fun m x =>
      b.toList.foldl (fun m y => accumulate m x y) m) ∅).toArray := by
  simp [mulPoly, accumulate, keyAdd, ← Array.foldl_toList]

theorem reflect_mulPoly (a b : Poly) : reflect (mulPoly a b) = reflect a * reflect b := by
  rw [mulPoly_eq_fold, reflect_outer]
  have hempty : reflect (∅ : Std.HashMap Key Rat).toArray = 0 := by
    simp [reflect, reflectList]
  rw [hempty, zero_add]
  rfl

theorem mulPoly_keys_nodup (a b : Poly) :
    ((mulPoly a b).toList.map Prod.fst).Nodup := by
  rw [mulPoly_eq_fold]
  exact hashMap_keys_nodup _

end Rhone.Computation.PolynomialEncoding
