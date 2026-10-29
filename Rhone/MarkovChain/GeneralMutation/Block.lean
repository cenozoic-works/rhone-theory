/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Defs

/-! # Block structure and linearity of the general-mutation-matrix right-hand side -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB ρ : F} {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

private theorem smul_sum1 {ι : Type*} [Fintype ι] (s : F) (w f : ι → F) :
    (∑ x, w x * (s * f x)) = s * ∑ x, w x * f x := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem rhsGen_zero (ξ : Config KA KB) : rhsGen θA θB ρ PA PB (fun _ => (0 : F)) ξ = 0 := by
  simp [rhsGen]

theorem rhsGen_add (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhsGen θA θB ρ PA PB (fun η => q₁ η + q₂ η) ξ
      = rhsGen θA θB ρ PA PB q₁ ξ + rhsGen θA θB ρ PA PB q₂ ξ := by
  simp only [rhsGen, mul_add, Finset.sum_add_distrib]
  ring

theorem rhsGen_smul (s : F) (q : Config KA KB → F) (ξ : Config KA KB) :
    rhsGen θA θB ρ PA PB (fun η => s * q η) ξ = s * rhsGen θA θB ρ PA PB q ξ := by
  simp only [rhsGen, smul_sum1, ← Finset.mul_sum]
  ring

theorem rhsGen_sub (q₁ q₂ : Config KA KB → F) (ξ : Config KA KB) :
    rhsGen θA θB ρ PA PB (fun η => q₁ η - q₂ η) ξ
      = rhsGen θA θB ρ PA PB q₁ ξ - rhsGen θA θB ρ PA PB q₂ ξ := by
  simp only [rhsGen, mul_sub, Finset.sum_sub_distrib]
  ring

theorem rhsGen_of_vanishing_below {h : Config KA KB → F} (ξ : Config KA KB)
    (hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB →
      (η.nA < ξ.nA ∨ η.nB < ξ.nB) → h η = 0) :
    rhsGen θA θB ρ PA PB h ξ
      = (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (ξ.mergeAB i j))
        + θA * (∑ i, ∑ k, PA k i * ((ξ.a i : ℕ) : F) * h (mutA ξ i k))
        + θA * (∑ i, ∑ j, ∑ k, PA k i * ((ξ.c i j : ℕ) : F) * h (mutCA ξ i j k))
        + θB * (∑ j, ∑ l, PB l j * ((ξ.b j : ℕ) : F) * h (mutB ξ j l))
        + θB * (∑ i, ∑ j, ∑ l, PB l j * ((ξ.c i j : ℕ) : F) * h (mutCB ξ i j l))
        + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.split i j) := by
  have e1 : (∑ i, ((ξ.coalA i : ℕ) : F) * h (ξ.dropA i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : ξ.a i = 0
    · rw [ξ.coalA_eq_zero_of hi]; simp
    · obtain ⟨h1, h2⟩ := ξ.dropA_lt hi
      rw [hb _ (le_of_lt h1) (le_of_eq h2) (Or.inl h1), mul_zero]
  have e2 : (∑ j, ((ξ.coalB j : ℕ) : F) * h (ξ.dropB j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : ξ.b j = 0
    · rw [ξ.coalB_eq_zero_of hj]; simp
    · obtain ⟨h1, h2⟩ := ξ.dropB_lt hj
      rw [hb _ (le_of_eq h1) (le_of_lt h2) (Or.inr h2), mul_zero]
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (ξ.dropC i j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : ξ.c i j = 0
    · rw [ξ.coalC_eq_zero_of hij]; simp
    · obtain ⟨h1, h2⟩ := ξ.dropC_lt hij
      rw [hb _ (le_of_lt h1) (le_of_lt h2) (Or.inl h1), mul_zero]
  simp only [rhsGen, e1, e2, e3, zero_add]

theorem rhsGen_congr {q₁ q₂ : Config KA KB → F} (ξ : Config KA KB)
    (h : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → q₁ η = q₂ η) :
    rhsGen θA θB ρ PA PB q₁ ξ = rhsGen θA θB ρ PA PB q₂ ξ := by
  set d : Config KA KB → F := fun η => q₁ η - q₂ η with hd
  have hdz : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → d η = 0 :=
    fun η h1 h2 => sub_eq_zero_of_eq (h η h1 h2)
  have key : rhsGen θA θB ρ PA PB d ξ = 0 := by
    rw [rhsGen_of_vanishing_below (θA := θA) (θB := θB) (ρ := ρ) (PA := PA) (PB := PB) ξ
      (fun η h1 h2 _ => hdz η h1 h2)]
    have m1 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * d (ξ.mergeAB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases ha : ξ.a i = 0
      · rw [ξ.coalAB_eq_zero_left j ha]; simp
      by_cases hbj : ξ.b j = 0
      · rw [ξ.coalAB_eq_zero_right i hbj]; simp
      obtain ⟨h1, h2⟩ := ξ.mergeAB_same ha hbj
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    have m2 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * d (ξ.split i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]; simp
      obtain ⟨h1, h2⟩ := ξ.split_same hc
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    have m3 : (∑ i, ∑ k, PA k i * ((ξ.a i : ℕ) : F) * d (mutA ξ i k)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases ha : ξ.a i = 0
      · rw [ha]; simp
      obtain ⟨h1, h2⟩ := mutA_same ξ i k ha
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    have m4 : (∑ i, ∑ j, ∑ k, PA k i * ((ξ.c i j : ℕ) : F) * d (mutCA ξ i j k)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
        Finset.sum_eq_zero fun k _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]; simp
      obtain ⟨h1, h2⟩ := mutCA_same ξ i j k hc
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    have m5 : (∑ j, ∑ l, PB l j * ((ξ.b j : ℕ) : F) * d (mutB ξ j l)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
      by_cases hbj : ξ.b j = 0
      · rw [hbj]; simp
      obtain ⟨h1, h2⟩ := mutB_same ξ j l hbj
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    have m6 : (∑ i, ∑ j, ∑ l, PB l j * ((ξ.c i j : ℕ) : F) * d (mutCB ξ i j l)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
        Finset.sum_eq_zero fun l _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]; simp
      obtain ⟨h1, h2⟩ := mutCB_same ξ i j l hc
      rw [hdz _ (le_of_eq h1) (le_of_eq h2), mul_zero]
    rw [m1, m2, m3, m4, m5, m6]
    ring
  rw [hd, rhsGen_sub] at key
  exact sub_eq_zero.mp key

end Rhone.MarkovChain.GeneralMutation
