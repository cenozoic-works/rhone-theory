/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Block structure of the killed-PIM recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)

namespace Config

theorem dropA_lt (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i ≠ 0) :
    (ξ.dropA i).nA < ξ.nA ∧ (ξ.dropA i).nB = ξ.nB :=
  ⟨by have := ξ.nA_dropA i h; omega, rfl⟩

theorem dropB_lt (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j ≠ 0) :
    (ξ.dropB j).nA = ξ.nA ∧ (ξ.dropB j).nB < ξ.nB :=
  ⟨rfl, by have := ξ.nB_dropB j h; omega⟩

theorem dropC_lt (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    (ξ.dropC i j).nA < ξ.nA ∧ (ξ.dropC i j).nB < ξ.nB :=
  ⟨by have := ξ.nA_dropC i j h; omega, by have := ξ.nB_dropC i j h; omega⟩

theorem killA_lt (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    (ξ.killA i j).nA < ξ.nA ∧ (ξ.killA i j).nB = ξ.nB :=
  ⟨by have := ξ.nA_killA i j h; omega, ξ.nB_killA i j h⟩

theorem killB_lt (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    (ξ.killB i j).nA = ξ.nA ∧ (ξ.killB i j).nB < ξ.nB :=
  ⟨ξ.nA_killB i j h, by have := ξ.nB_killB i j h; omega⟩

theorem mergeAB_same (ξ : Config KA KB) {i : Fin KA} {j : Fin KB}
    (ha : ξ.a i ≠ 0) (hb : ξ.b j ≠ 0) :
    (ξ.mergeAB i j).nA = ξ.nA ∧ (ξ.mergeAB i j).nB = ξ.nB :=
  ⟨ξ.nA_mergeAB i j ha, ξ.nB_mergeAB i j hb⟩

theorem split_same (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    (ξ.split i j).nA = ξ.nA ∧ (ξ.split i j).nB = ξ.nB :=
  ⟨ξ.nA_split i j h, ξ.nB_split i j h⟩

end Config

theorem rhs_zero (ξ : Config KA KB) : rhs θA θB ρ πA πB (fun _ => (0 : F)) ξ = 0 := by
  simp [rhs]

theorem rhs_add (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun η => q₁ η + q₂ η) ξ
      = rhs θA θB ρ πA πB q₁ ξ + rhs θA θB ρ πA πB q₂ ξ := by
  simp only [rhs, mul_add, Finset.sum_add_distrib]
  ring

theorem rhs_smul (c : F) (q : Config KA KB → F) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun η => c * q η) ξ = c * rhs θA θB ρ πA πB q ξ := by
  have gen : ∀ {ι : Type} [Fintype ι] (w : ι → F) (f : ι → F),
      (∑ i, w i * (c * f i)) = c * ∑ i, w i * f i := by
    intro ι _ w f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have s5 : (∑ i, πA i * (((ξ.a i : ℕ) : F) * (c * q (ξ.dropA i))
        + ∑ j, ((ξ.c i j : ℕ) : F) * (c * q (ξ.killA i j))))
      = c * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gen (fun j => ((ξ.c i j : ℕ) : F)) (fun j => q (ξ.killA i j))]
    ring
  have s6 : (∑ j, πB j * (((ξ.b j : ℕ) : F) * (c * q (ξ.dropB j))
        + ∑ i, ((ξ.c i j : ℕ) : F) * (c * q (ξ.killB i j))))
      = c * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gen (fun i => ((ξ.c i j : ℕ) : F)) (fun i => q (ξ.killB i j))]
    ring
  have s3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * (c * q (ξ.dropC i j)))
      = c * ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => gen _ _
  have s4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * (c * q (ξ.mergeAB i j)))
      = c * ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => gen _ _
  have s7 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * (c * q (ξ.split i j)))
      = c * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => gen _ _
  simp only [rhs]
  rw [gen (fun i => ((ξ.coalA i : ℕ) : F)) (fun i => q (ξ.dropA i)),
    gen (fun j => ((ξ.coalB j : ℕ) : F)) (fun j => q (ξ.dropB j)), s3, s4, s5, s6, s7]
  ring

theorem rhs_sub (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ
      = rhs θA θB ρ πA πB q₁ ξ - rhs θA θB ρ πA πB q₂ ξ := by
  simp only [rhs, mul_sub, Finset.sum_sub_distrib, sub_add_sub_comm]

theorem rhs_of_vanishing_below {h : Config KA KB → F} (ξ : Config KA KB)
    (hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB →
      (η.nA < ξ.nA ∨ η.nB < ξ.nB) → h η = 0) :
    rhs θA θB ρ πA πB h ξ
      = (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (ξ.mergeAB i j))
        + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.split i j) := by
  have hdropA : ∀ i : Fin KA, h (ξ.dropA i) = 0 ∨ ξ.a i = 0 := by
    intro i
    by_cases hi : ξ.a i = 0
    · exact Or.inr hi
    · obtain ⟨h1, h2⟩ := ξ.dropA_lt hi
      exact Or.inl (hb _ (le_of_lt h1) (le_of_eq h2) (Or.inl h1))
  have hdropB : ∀ j : Fin KB, h (ξ.dropB j) = 0 ∨ ξ.b j = 0 := by
    intro j
    by_cases hj : ξ.b j = 0
    · exact Or.inr hj
    · obtain ⟨h1, h2⟩ := ξ.dropB_lt hj
      exact Or.inl (hb _ (le_of_eq h1) (le_of_lt h2) (Or.inr h2))
  have hdropC : ∀ (i : Fin KA) (j : Fin KB), h (ξ.dropC i j) = 0 ∨ ξ.c i j = 0 := by
    intro i j
    by_cases hij : ξ.c i j = 0
    · exact Or.inr hij
    · obtain ⟨h1, h2⟩ := ξ.dropC_lt hij
      exact Or.inl (hb _ (le_of_lt h1) (le_of_lt h2) (Or.inl h1))
  have hkillA : ∀ (i : Fin KA) (j : Fin KB), h (ξ.killA i j) = 0 ∨ ξ.c i j = 0 := by
    intro i j
    by_cases hij : ξ.c i j = 0
    · exact Or.inr hij
    · obtain ⟨h1, h2⟩ := ξ.killA_lt hij
      exact Or.inl (hb _ (le_of_lt h1) (le_of_eq h2) (Or.inl h1))
  have hkillB : ∀ (i : Fin KA) (j : Fin KB), h (ξ.killB i j) = 0 ∨ ξ.c i j = 0 := by
    intro i j
    by_cases hij : ξ.c i j = 0
    · exact Or.inr hij
    · obtain ⟨h1, h2⟩ := ξ.killB_lt hij
      exact Or.inl (hb _ (le_of_eq h1) (le_of_lt h2) (Or.inr h2))
  have e1 : (∑ i, ((ξ.coalA i : ℕ) : F) * h (ξ.dropA i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hdropA i with h0 | h0
    · rw [h0, mul_zero]
    · rw [ξ.coalA_eq_zero_of h0]; simp
  have e2 : (∑ j, ((ξ.coalB j : ℕ) : F) * h (ξ.dropB j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases hdropB j with h0 | h0
    · rw [h0, mul_zero]
    · rw [ξ.coalB_eq_zero_of h0]; simp
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (ξ.dropC i j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rcases hdropC i j with h0 | h0
    · rw [h0, mul_zero]
    · rw [ξ.coalC_eq_zero_of h0]; simp
  have e5 : (∑ i, πA i * (((ξ.a i : ℕ) : F) * h (ξ.dropA i)
      + ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.killA i j))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have t1 : ((ξ.a i : ℕ) : F) * h (ξ.dropA i) = 0 := by
      rcases hdropA i with h0 | h0
      · rw [h0, mul_zero]
      · rw [h0]; simp
    have t2 : (∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.killA i j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases hkillA i j with h0 | h0
      · rw [h0, mul_zero]
      · rw [h0]; simp
    rw [t1, t2, add_zero, mul_zero]
  have e6 : (∑ j, πB j * (((ξ.b j : ℕ) : F) * h (ξ.dropB j)
      + ∑ i, ((ξ.c i j : ℕ) : F) * h (ξ.killB i j))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have t1 : ((ξ.b j : ℕ) : F) * h (ξ.dropB j) = 0 := by
      rcases hdropB j with h0 | h0
      · rw [h0, mul_zero]
      · rw [h0]; simp
    have t2 : (∑ i, ((ξ.c i j : ℕ) : F) * h (ξ.killB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hkillB i j with h0 | h0
      · rw [h0, mul_zero]
      · rw [h0]; simp
    rw [t1, t2, add_zero, mul_zero]
  simp only [rhs, e1, e2, e3, e5, e6, mul_zero, zero_add, add_zero]

theorem rhs_congr {q₁ q₂ : Config KA KB → F} (ξ : Config KA KB)
    (h : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → q₁ η = q₂ η) :
    rhs θA θB ρ πA πB q₁ ξ = rhs θA θB ρ πA πB q₂ ξ := by
  have key : rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ = 0 := by
    rw [rhs_of_vanishing_below θA θB ρ πA πB ξ
      (fun η h1 h2 _ => sub_eq_zero_of_eq (h η h1 h2))]
    have m1 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * (q₁ (ξ.mergeAB i j) - q₂ (ξ.mergeAB i j)))
        = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases ha : ξ.a i = 0
      · rw [ξ.coalAB_eq_zero_left j ha]; simp
      by_cases hbj : ξ.b j = 0
      · rw [ξ.coalAB_eq_zero_right i hbj]; simp
      obtain ⟨h1, h2⟩ := ξ.mergeAB_same ha hbj
      rw [sub_eq_zero_of_eq (h _ (le_of_eq h1) (le_of_eq h2)), mul_zero]
    have m2 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * (q₁ (ξ.split i j) - q₂ (ξ.split i j))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]; simp
      obtain ⟨h1, h2⟩ := ξ.split_same hc
      rw [sub_eq_zero_of_eq (h _ (le_of_eq h1) (le_of_eq h2)), mul_zero]
    rw [m1, m2, mul_zero, add_zero]
  rw [rhs_sub] at key
  exact sub_eq_zero.mp key

end Rhone.LinearAlgebra.Recursion
