/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Block

/-!
# The two-locus infinite-alleles recursion

Source: golding1984, Appendix 1, p. 273; jenkins_song2010, eq. 2.5. -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]

def dropIndA (ξ : Config KA KB) (i : Fin KA) : ℕ :=
  if ξ.a i = 1 ∧ ξ.cRow i = 0 then 1 else 0

def killIndA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ :=
  if ξ.mA i = 1 ∧ ξ.c i j = 1 then 1 else 0

def dropIndB (ξ : Config KA KB) (j : Fin KB) : ℕ :=
  if ξ.b j = 1 ∧ ξ.cCol j = 0 then 1 else 0

def killIndB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ :=
  if ξ.mB j = 1 ∧ ξ.c i j = 1 then 1 else 0

theorem dropIndA_eq_zero_of (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i = 0) :
    dropIndA ξ i = 0 := by
  simp [dropIndA, h]

theorem killIndA_eq_zero_of (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j = 0) :
    killIndA ξ i j = 0 := by
  simp [killIndA, h]

theorem dropIndB_eq_zero_of (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j = 0) :
    dropIndB ξ j = 0 := by
  simp [dropIndB, h]

theorem killIndB_eq_zero_of (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j = 0) :
    killIndB ξ i j = 0 := by
  simp [killIndB, h]

theorem mA_eq_one_of_dropIndA (ξ : Config KA KB) {i : Fin KA} (h : dropIndA ξ i ≠ 0) :
    ξ.mA i = 1 := by
  by_cases hc : ξ.a i = 1 ∧ ξ.cRow i = 0
  · simp [mA, hc.1, hc.2]
  · simp [dropIndA, hc] at h

theorem mA_eq_one_of_killIndA (ξ : Config KA KB) {i : Fin KA} {j : Fin KB}
    (h : killIndA ξ i j ≠ 0) : ξ.mA i = 1 := by
  by_cases hc : ξ.mA i = 1 ∧ ξ.c i j = 1
  · exact hc.1
  · simp [killIndA, hc] at h

theorem mB_eq_one_of_dropIndB (ξ : Config KA KB) {j : Fin KB} (h : dropIndB ξ j ≠ 0) :
    ξ.mB j = 1 := by
  by_cases hc : ξ.b j = 1 ∧ ξ.cCol j = 0
  · simp [mB, hc.1, hc.2]
  · simp [dropIndB, hc] at h

theorem mB_eq_one_of_killIndB (ξ : Config KA KB) {i : Fin KA} {j : Fin KB}
    (h : killIndB ξ i j ≠ 0) : ξ.mB j = 1 := by
  by_cases hc : ξ.mB j = 1 ∧ ξ.c i j = 1
  · exact hc.1
  · simp [killIndB, hc] at h

def rhsIA (θA θB ρ : F) (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
    + θA * ∑ i, (((dropIndA ξ i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * q (ξ.killA i j))
    + θB * ∑ j, (((dropIndB ξ j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * q (ξ.killB i j))
    + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

structure IsSolutionIA (θA θB ρ : F) (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = 1
  bdryB : ∀ j, q (Config.eB j) = 1
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB →
    diag θA θB ρ ξ * q ξ = rhsIA θA θB ρ q ξ

variable (θA θB ρ : F)

theorem rhsIA_zero (ξ : Config KA KB) : rhsIA θA θB ρ (fun _ => (0 : F)) ξ = 0 := by
  simp [rhsIA]

theorem rhsIA_add (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ (fun η => q₁ η + q₂ η) ξ
      = rhsIA θA θB ρ q₁ ξ + rhsIA θA θB ρ q₂ ξ := by
  simp only [rhsIA, mul_add, Finset.sum_add_distrib]
  ring

theorem rhsIA_smul (c : F) (q : Config KA KB → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ (fun η => c * q η) ξ = c * rhsIA θA θB ρ q ξ := by
  have gen : ∀ {ι : Type} [Fintype ι] (w : ι → F) (f : ι → F),
      (∑ i, w i * (c * f i)) = c * ∑ i, w i * f i := by
    intro ι _ w f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have s5 : (∑ i, (((dropIndA ξ i : ℕ) : F) * (c * q (ξ.dropA i))
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * (c * q (ξ.killA i j))))
      = c * ∑ i, (((dropIndA ξ i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * q (ξ.killA i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gen (fun j => ((killIndA ξ i j : ℕ) : F)) (fun j => q (ξ.killA i j))]
    ring
  have s6 : (∑ j, (((dropIndB ξ j : ℕ) : F) * (c * q (ξ.dropB j))
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * (c * q (ξ.killB i j))))
      = c * ∑ j, (((dropIndB ξ j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * q (ξ.killB i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gen (fun i => ((killIndB ξ i j : ℕ) : F)) (fun i => q (ξ.killB i j))]
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
  simp only [rhsIA]
  rw [gen (fun i => ((ξ.coalA i : ℕ) : F)) (fun i => q (ξ.dropA i)),
    gen (fun j => ((ξ.coalB j : ℕ) : F)) (fun j => q (ξ.dropB j)), s3, s4, s5, s6, s7]
  ring

theorem rhsIA_sub (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ (fun η => q₁ η - q₂ η) ξ
      = rhsIA θA θB ρ q₁ ξ - rhsIA θA θB ρ q₂ ξ := by
  simp only [rhsIA, mul_sub, Finset.sum_sub_distrib, sub_add_sub_comm]

theorem rhsIA_of_vanishing_below {h : Config KA KB → F} (ξ : Config KA KB)
    (hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB →
      (η.nA < ξ.nA ∨ η.nB < ξ.nB) → h η = 0) :
    rhsIA θA θB ρ h ξ
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
  have e5 : (∑ i, (((dropIndA ξ i : ℕ) : F) * h (ξ.dropA i)
      + ∑ j, ((killIndA ξ i j : ℕ) : F) * h (ξ.killA i j))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have t1 : ((dropIndA ξ i : ℕ) : F) * h (ξ.dropA i) = 0 := by
      rcases hdropA i with h0 | h0
      · rw [h0, mul_zero]
      · rw [dropIndA_eq_zero_of ξ h0]; simp
    have t2 : (∑ j, ((killIndA ξ i j : ℕ) : F) * h (ξ.killA i j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases hkillA i j with h0 | h0
      · rw [h0, mul_zero]
      · rw [killIndA_eq_zero_of ξ h0]; simp
    rw [t1, t2, add_zero]
  have e6 : (∑ j, (((dropIndB ξ j : ℕ) : F) * h (ξ.dropB j)
      + ∑ i, ((killIndB ξ i j : ℕ) : F) * h (ξ.killB i j))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have t1 : ((dropIndB ξ j : ℕ) : F) * h (ξ.dropB j) = 0 := by
      rcases hdropB j with h0 | h0
      · rw [h0, mul_zero]
      · rw [dropIndB_eq_zero_of ξ h0]; simp
    have t2 : (∑ i, ((killIndB ξ i j : ℕ) : F) * h (ξ.killB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hkillB i j with h0 | h0
      · rw [h0, mul_zero]
      · rw [killIndB_eq_zero_of ξ h0]; simp
    rw [t1, t2, add_zero]
  simp only [rhsIA, e1, e2, e3, e5, e6, mul_zero, zero_add, add_zero]

theorem rhsIA_congr {q₁ q₂ : Config KA KB → F} (ξ : Config KA KB)
    (h : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → q₁ η = q₂ η) :
    rhsIA θA θB ρ q₁ ξ = rhsIA θA θB ρ q₂ ξ := by
  have key : rhsIA θA θB ρ (fun η => q₁ η - q₂ η) ξ = 0 := by
    rw [rhsIA_of_vanishing_below θA θB ρ ξ
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
  rw [rhsIA_sub] at key
  exact sub_eq_zero.mp key

end Rhone.Probability.InfiniteAlleles
