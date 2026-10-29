/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerCountFibersProof
public import Rhone.Computation.CheckerNormalizationSpec

/-! # Multinomial multiplicity of an ordered fully typed sample -/

@[expose] public section
namespace Rhone.Computation.CheckerSpec

open Finset LinearAlgebra.Recursion Coalescent.TwoLocusGenealogy Probability.InfiniteAlleles

noncomputable def orderedProfile (n : Nat) (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    Finset ((Fin n → Fin 2) × (Fin n → Fin 2)) := by
  classical
  exact univ.filter fun p => cSample p.1 p.2 = ξ

theorem cSample_eq_iff {n : Nat} (a b : Fin n → Fin 2)
    (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2)
    (ha : ξ.a = fun _ => 0) (hb : ξ.b = fun _ => 0) :
    cSample a b = ξ ↔ ∀ cell : Fin 2 × Fin 2,
      fibreCard (fun k => (a k, b k)) cell = ξ.c cell.1 cell.2 := by
  have hcount : ∀ i j, fibreCard (fun k => (a k, b k)) (i, j) = (cSample a b).c i j := by
    intro i j
    simp only [fibreCard, cSample, Prod.mk.injEq]
  constructor
  · intro h cell
    rw [hcount, h]
  · intro h
    apply Rhone.LinearAlgebra.Recursion.Config.ext
    · exact ha.symm
    · exact hb.symm
    · funext i j
      exact (hcount i j).symm.trans (h (i, j))

theorem card_orderedProfile_mul {n : Nat} (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2)
    (ha : ξ.a = fun _ => 0) (hb : ξ.b = fun _ => 0) (ht : ξ.t = n) :
    (orderedProfile n ξ).card * ∏ i, ∏ j, Nat.factorial (ξ.c i j) = Nat.factorial n := by
  classical
  let counts := fun cell : Fin 2 × Fin 2 => ξ.c cell.1 cell.2
  have htotal : ∑ cell, counts cell = n := by
    rw [Fintype.sum_prod_type]
    exact ht
  have hcard : (orderedProfile n ξ).card =
      (univ.filter fun f : Fin n → Fin 2 × Fin 2 =>
        ∀ cell, fibreCard f cell = counts cell).card := by
    let e := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2) (fun _ => Fin 2)).symm
    refine Finset.card_equiv e fun p => ?_
    simp only [orderedProfile, mem_filter, mem_univ, true_and]
    exact cSample_eq_iff p.1 p.2 ξ ha hb
  rw [hcard, ← Fintype.prod_prod_type (f := fun cell : Fin 2 × Fin 2 =>
    Nat.factorial (ξ.c cell.1 cell.2))]
  exact card_profile_mul counts htotal

end Rhone.Computation.CheckerSpec
