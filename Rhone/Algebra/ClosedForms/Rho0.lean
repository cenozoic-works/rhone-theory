/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.ClosedForms.Overcount
public import Rhone.LinearAlgebra.Recursion.Block

/-! # The `ρ = 0` denominator support, from the recursion -/

@[expose] public section

namespace Rhone.Algebra.ClosedForms

open Finset LinearAlgebra.Recursion Config

variable {KA KB : ℕ}

def meas (ξ : Config KA KB) : ℕ := ξ.n + ξ.nA + ξ.nB

def Below (η ξ : Config KA KB) : Prop := η.n ≤ ξ.n ∧ η.nA ≤ ξ.nA ∧ η.nB ≤ ξ.nB

theorem Below.rfl (ξ : Config KA KB) : Below ξ ξ := ⟨le_rfl, le_rfl, le_rfl⟩

theorem Below.trans {η ζ ξ : Config KA KB} (h₁ : Below η ζ) (h₂ : Below ζ ξ) : Below η ξ :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₁.2.1 h₂.2.1, le_trans h₁.2.2 h₂.2.2⟩

def Step (η ξ : Config KA KB) : Prop := Below η ξ ∧ meas η < meas ξ

theorem step_dropA (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i ≠ 0) : Step (ξ.dropA i) ξ := by
  have h1 := ξ.n_dropA i h
  have h2 := ξ.nA_dropA i h
  have h3 := ξ.nB_dropA i
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

theorem step_dropB (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j ≠ 0) : Step (ξ.dropB j) ξ := by
  have h1 := ξ.n_dropB j h
  have h2 := ξ.nA_dropB j
  have h3 := ξ.nB_dropB j h
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

theorem step_dropC (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Step (ξ.dropC i j) ξ := by
  have h1 := ξ.n_dropC i j h
  have h2 := ξ.nA_dropC i j h
  have h3 := ξ.nB_dropC i j h
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

theorem step_mergeAB (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (ha : ξ.a i ≠ 0)
    (hb : ξ.b j ≠ 0) : Step (ξ.mergeAB i j) ξ := by
  have h1 := ξ.n_mergeAB i j ha hb
  have h2 := ξ.nA_mergeAB i j ha
  have h3 := ξ.nB_mergeAB i j hb
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

theorem step_killA (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Step (ξ.killA i j) ξ := by
  have h1 := ξ.n_killA i j h
  have h2 := ξ.nA_killA i j h
  have h3 := ξ.nB_killA i j h
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

theorem step_killB (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Step (ξ.killB i j) ξ := by
  have h1 := ξ.n_killB i j h
  have h2 := ξ.nA_killB i j h
  have h3 := ξ.nB_killB i j h
  exact ⟨⟨by omega, by omega, by omega⟩, by simp only [meas]; omega⟩

variable {F : Type*} [CommRing F]

theorem q_mem_of_rho_zero {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q : Config KA KB → F} (hq : IsSolution θA θB 0 πA πB q)
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (ξ : Config KA KB)
    (hstop : ∀ η : Config KA KB, Below η ξ → min η.nA η.nB ≤ 1 → q η ∈ A)
    (hinv : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB →
      ∃ y ∈ A, diag θA θB 0 η * y = 1) :
    q ξ ∈ A := by
  have main : ∀ M : ℕ, ∀ η : Config KA KB, meas η = M → Below η ξ → q η ∈ A := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M IH =>
      intro η hmeas hbelow
      by_cases hmin : min η.nA η.nB ≤ 1
      · exact hstop η hbelow hmin
      have h2min : 2 ≤ min η.nA η.nB := by omega
      have hnA : 2 ≤ η.nA := le_trans h2min (min_le_left _ _)
      have hn : 2 ≤ η.n := le_trans hnA η.nA_le_n
      obtain ⟨y, hyA, hy⟩ := hinv η hbelow h2min
      have hrec := hq.recursion η hn
      have hqval : q η = y * rhs θA θB 0 πA πB q η := by
        calc q η = (diag θA θB 0 η * y) * q η := by rw [hy, one_mul]
          _ = y * (diag θA θB 0 η * q η) := by ring
          _ = y * rhs θA θB 0 πA πB q η := by rw [hrec]
      have term : ∀ (cf : ℕ) (ζ : Config KA KB), (cf ≠ 0 → Step ζ η) →
          ((cf : ℕ) : F) * q ζ ∈ A := by
        intro cf ζ hstep
        rcases Nat.eq_zero_or_pos cf with h0 | h0
        · rw [h0]; simp
        · obtain ⟨hb, hlt⟩ := hstep (by omega)
          exact A.mul_mem (natCast_mem A cf)
            (IH (meas ζ) (by omega) ζ rfl (hb.trans hbelow))
      have hcoalA : ∀ i : Fin KA, ((η.coalA i : ℕ) : F) * q (η.dropA i) ∈ A := fun i =>
        term _ _ fun hcf => step_dropA η fun h0 => hcf (η.coalA_eq_zero_of h0)
      have hcoalB : ∀ j : Fin KB, ((η.coalB j : ℕ) : F) * q (η.dropB j) ∈ A := fun j =>
        term _ _ fun hcf => step_dropB η fun h0 => hcf (η.coalB_eq_zero_of h0)
      have hcoalC : ∀ (i : Fin KA) (j : Fin KB),
          ((η.coalC i j : ℕ) : F) * q (η.dropC i j) ∈ A := fun i j =>
        term _ _ fun hcf => step_dropC η fun h0 => hcf (η.coalC_eq_zero_of h0)
      have hcoalAB : ∀ (i : Fin KA) (j : Fin KB),
          ((η.coalAB i j : ℕ) : F) * q (η.mergeAB i j) ∈ A := by
        intro i j
        refine term _ _ fun hcf => step_mergeAB η ?_ ?_
        · exact fun h0 => hcf (η.coalAB_eq_zero_left j h0)
        · exact fun h0 => hcf (η.coalAB_eq_zero_right i h0)
      have hdropA : ∀ i : Fin KA, ((η.a i : ℕ) : F) * q (η.dropA i) ∈ A := fun i =>
        term _ _ fun hcf => step_dropA η hcf
      have hdropB : ∀ j : Fin KB, ((η.b j : ℕ) : F) * q (η.dropB j) ∈ A := fun j =>
        term _ _ fun hcf => step_dropB η hcf
      have hkillA : ∀ (i : Fin KA) (j : Fin KB),
          ((η.c i j : ℕ) : F) * q (η.killA i j) ∈ A := fun i j =>
        term _ _ fun hcf => step_killA η hcf
      have hkillB : ∀ (i : Fin KA) (j : Fin KB),
          ((η.c i j : ℕ) : F) * q (η.killB i j) ∈ A := fun i j =>
        term _ _ fun hcf => step_killB η hcf
      rw [hqval]
      refine A.mul_mem hyA ?_
      simp only [rhs]
      refine A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem ?_ ?_) ?_) ?_)
        (A.mul_mem hθA ?_)) (A.mul_mem hθB ?_)) ?_
      · exact A.sum_mem fun i _ => hcoalA i
      · exact A.sum_mem fun j _ => hcoalB j
      · exact A.sum_mem fun i _ => A.sum_mem fun j _ => hcoalC i j
      · exact A.sum_mem fun i _ => A.sum_mem fun j _ => hcoalAB i j
      · exact A.sum_mem fun i _ =>
          A.mul_mem (hπA i) (A.add_mem (hdropA i) (A.sum_mem fun j _ => hkillA i j))
      · exact A.sum_mem fun j _ =>
          A.mul_mem (hπB j) (A.add_mem (hdropB j) (A.sum_mem fun i _ => hkillB i j))
      · rw [zero_mul]; exact A.zero_mem
  exact main (meas ξ) ξ rfl (Below.rfl ξ)

end Rhone.Algebra.ClosedForms
