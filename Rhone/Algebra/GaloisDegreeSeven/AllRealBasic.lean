/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive
public import Rhone.LinearAlgebra.Tridiag.RhoDegree
public import Mathlib.Topology.Algebra.Polynomial

/-! # `E_{i,j}` as a polynomial in `ρ`, and the "many roots ⟹ splits" step -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial LinearAlgebra.Tridiag

noncomputable def Epoly (F : Type*) [CommRing F] (i j : ℕ) (θA θB : F) : F[X] :=
  E F[X] i j (C θA) (C θB) X

theorem eval_Epoly {F : Type*} [CommRing F] (i j : ℕ) (θA θB x : F) :
    (Epoly F i j θA θB).eval x = E F i j θA θB x := by
  have h := E_map (Polynomial.evalRingHom x) i j (C θA) (C θB) X
  simpa [Epoly] using h

section Order

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

theorem kappaT_pos {i j : ℕ} {θA θB : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) : 0 < kappaT i j θA θB := by
  have h1 : (2 : F) ≤ (i : F) := by exact_mod_cast hi
  have h2 : (2 : F) ≤ (j : F) := by exact_mod_cast hj
  unfold kappaT
  nlinarith

variable [NoZeroDivisors F] [CharZero F]

theorem natDegree_Epoly {i j : ℕ} {θA θB : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) : (Epoly F i j θA θB).natDegree = min i j :=
  natDegree_E_of_charZero i j θA θB (kappaT_pos hi hj hA hB).ne'

theorem Epoly_ne_zero {i j : ℕ} {θA θB : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) : Epoly F i j θA θB ≠ 0 := by
  intro h
  have hd := natDegree_Epoly hi hj hA hB (F := F)
  rw [h, natDegree_zero] at hd
  omega

omit [NoZeroDivisors F] [CharZero F] in
theorem Epoly_root_neg {i j : ℕ} {θA θB x : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hx : (Epoly F i j θA θB).eval x = 0) : x < 0 := by
  by_contra h
  rw [eval_Epoly] at hx
  exact LinearAlgebra.GaloisDegreeSeven.E_ne_zero hi hj hA hB (not_lt.mp h) hx

end Order

theorem card_roots_eq_of_card_le {F : Type*} [Field F] {p : F[X]} (hp : p ≠ 0) (T : Finset F)
    (hT : ∀ x ∈ T, p.eval x = 0) (hcard : p.natDegree ≤ T.card) :
    Multiset.card p.roots = p.natDegree ∧ p.Splits := by
  classical
  have hsub : T ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hp, hT x hx⟩
  have h1 : T.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card p.roots ≤ p.natDegree := p.card_roots'
  have hcards : Multiset.card p.roots = p.natDegree := by omega
  exact ⟨hcards, splits_iff_card_roots.mpr hcards⟩

end Rhone.Algebra.GaloisDegreeSeven
