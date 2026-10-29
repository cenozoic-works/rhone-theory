/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialSupportProof
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Sparse assembly is the coefficient functional -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

noncomputable def momentSum (g : MvPolynomial (Fin 3) Rat)
    (value : Nat → Nat → Nat → Rat) : Rat :=
  (AddMonoidAlgebra.coeff g).sum fun d v => v * value (d 0) (d 1) (d 2)

theorem momentSum_add (a b : MvPolynomial (Fin 3) Rat)
    (value : Nat → Nat → Nat → Rat) :
    momentSum (a + b) value = momentSum a value + momentSum b value := by
  unfold momentSum
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index' (fun _ => zero_mul _)
  intro d x y
  exact add_mul x y _

theorem momentSum_monomial (key : Key) (v : Rat)
    (value : Nat → Nat → Nat → Rat) :
    momentSum (MvPolynomial.monomial (exponent key) v) value =
      v * value key.1 key.2.1 key.2.2 := by
  simp [momentSum, MvPolynomial.monomial, exponent]

theorem momentSum_reflectList (terms : List (Key × Rat))
    (value : Nat → Nat → Nat → Rat) :
    momentSum (reflectList terms) value =
      (terms.map fun term => term.2 * value term.1.1 term.1.2.1 term.1.2.2).sum := by
  induction terms with
  | nil => simp [reflectList, momentSum]
  | cons term terms ih =>
    simp only [reflectList] at ih
    simp only [reflectList, List.map_cons, List.sum_cons]
    rw [momentSum_add, momentSum_monomial, ih]

private theorem assemble_fold (terms : List (Key × Rat)) (tab : PhiTable) (acc : Rat) :
    terms.foldl (fun acc term => acc + term.2 * tab.get term.1.1 term.1.2.1 term.1.2.2) acc =
      acc + (terms.map fun term => term.2 * tab.get term.1.1 term.1.2.1 term.1.2.2).sum := by
  induction terms generalizing acc with
  | nil => simp
  | cons term terms ih => simp [ih, add_assoc]

theorem assemble_eq_momentSum (tab : PhiTable) (g : Poly) :
    assemble tab g = momentSum (reflect g) tab.get := by
  rw [show assemble tab g = g.toList.foldl
    (fun acc term => acc + term.2 * tab.get term.1.1 term.1.2.1 term.1.2.2) 0 by
      simp [assemble, ← Array.foldl_toList]]
  rw [assemble_fold, zero_add]
  exact (momentSum_reflectList g.toList tab.get).symm

theorem momentSum_congr {g : MvPolynomial (Fin 3) Rat} {na nb nl : Nat}
    (h : Supported g na nb nl) (a b : Nat → Nat → Nat → Rat)
    (he : ∀ i j t, i ≤ na → j ≤ nb → t ≤ min i j → a i j t = b i j t) :
    momentSum g a = momentSum g b := by
  unfold momentSum
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨ha, hb, _, ht0, ht1⟩ := h d hd
  rw [he (d 0) (d 1) (d 2) ha hb (le_min ht0 ht1)]

private theorem exponent_coordinates (d : Fin 3 →₀ Nat) :
    exponent (d 0, d 1, d 2) = d := by
  ext i
  fin_cases i <;> simp [exponent]

theorem momentSum_eq_triple {g : MvPolynomial (Fin 3) Rat} {na nb nl : Nat}
    (h : Supported g na nb nl) (value : Nat → Nat → Nat → Rat) :
    momentSum g value =
      ∑ i ∈ Finset.range (na + 1), ∑ j ∈ Finset.range (nb + 1),
        ∑ t ∈ Finset.range (nl + 1),
          g.coeff (exponent (i, j, t)) * value i j t := by
  let box := (Finset.range (na + 1)).product
    ((Finset.range (nb + 1)).product (Finset.range (nl + 1)))
  let emb : Key ↪ (Fin 3 →₀ Nat) := ⟨exponent, exponent_injective⟩
  have hs : g.support ⊆ box.map emb := by
    intro d hd
    obtain ⟨ha, hb, hl, _, _⟩ := h d hd
    apply Finset.mem_map.mpr
    refine ⟨(d 0, d 1, d 2), ?_, exponent_coordinates d⟩
    simp [box, Finset.mem_product, Finset.mem_range, ha, hb, hl]
  rw [momentSum, Finsupp.sum_of_support_subset (AddMonoidAlgebra.coeff g) hs _ (by simp)]
  rw [Finset.sum_map]
  simp [box, emb, Finset.sum_product, exponent]

end Rhone.Computation.PolynomialEncoding
