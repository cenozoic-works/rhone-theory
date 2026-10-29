/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Mutation generators, parent-independent mutation, and the general-matrix recursion -/

@[expose] public section

namespace Rhone.MarkovChain.Biallelic

open Finset LinearAlgebra.Recursion

variable {K KA KB : ℕ} {F : Type*} [Field F]

def IsGenerator (G : Fin K → Fin K → F) : Prop := ∀ i, ∑ j, G i j = 0

def pimGen (θ : F) (π : Fin K → F) : Fin K → Fin K → F :=
  fun i j => θ / 2 * (π j - if i = j then 1 else 0)

theorem pimGen_of_ne (θ : F) (π : Fin K → F) {i j : Fin K} (h : i ≠ j) :
    pimGen θ π i j = θ / 2 * π j := by
  simp [pimGen, h]

theorem pimGen_self (θ : F) (π : Fin K → F) (i : Fin K) :
    pimGen θ π i i = θ / 2 * (π i - 1) := by
  simp [pimGen]

theorem isGenerator_pimGen {θ : F} {π : Fin K → F} (hπ : ∑ i, π i = 1) :
    IsGenerator (pimGen θ π) := by
  intro i
  simp only [pimGen, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ]
  simp

def IsPIM (θ : F) (π : Fin K → F) (G : Fin K → Fin K → F) : Prop := G = pimGen θ π

structure IsProbVec [LE F] (π : Fin K → F) : Prop where
  nonneg : ∀ i, 0 ≤ π i
  sum_eq_one : ∑ i, π i = 1

def jump (θ : F) (G : Fin K → Fin K → F) : Fin K → Fin K → F :=
  fun i j => (if i = j then 1 else 0) + 2 / θ * G i j

theorem sum_jump {θ : F} {G : Fin K → Fin K → F} (hG : IsGenerator G) (i : Fin K) :
    ∑ j, jump θ G i j = 1 := by
  simp only [jump, Finset.sum_add_distrib, ← Finset.mul_sum, hG i, mul_zero, add_zero]
  simp

theorem jump_pimGen {θ : F} (h2 : (2 : F) ≠ 0) (hθ : θ ≠ 0) (π : Fin K → F) :
    jump θ (pimGen θ π) = fun _ j => π j := by
  funext i j
  simp only [jump, pimGen]
  field_simp
  split_ifs <;> ring

def wgt (π : Fin K → F) (P : Fin K → Fin K → F) : Fin K → F := fun i => ∑ k, π k * P k i

theorem wgt_const_rows {π : Fin K → F} (hπ : ∑ i, π i = 1) :
    wgt π (fun _ j => π j) = π := by
  funext i
  simp [wgt, ← Finset.sum_mul, hπ]

structure IsSolutionP (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F) (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = πA i
  bdryB : ∀ j, q (Config.eB j) = πB j
  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
    diag θA θB ρ ξ * q ξ = rhs θA θB ρ (wgt πA PA) (wgt πB PB) q ξ

theorem rhs_of_wgt_eq {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}
    (hA : wgt πA PA = πA) (hB : wgt πB PB = πB) (q : Config KA KB → F) (ξ : Config KA KB) :
    rhs θA θB ρ (wgt πA PA) (wgt πB PB) q ξ = rhs θA θB ρ πA πB q ξ := by
  rw [hA, hB]

theorem isSolutionP_iff {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}
    (hA : wgt πA PA = πA) (hB : wgt πB PB = πB) (q : Config KA KB → F) :
    IsSolutionP θA θB ρ πA πB PA PB q ↔ IsSolution θA θB ρ πA πB q := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, h1, h2, h3, fun ξ hξ => by rw [h4 ξ hξ, rhs_of_wgt_eq hA hB]⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, h1, h2, h3, fun ξ hξ => by rw [rhs_of_wgt_eq hA hB, h4 ξ hξ]⟩

end Rhone.MarkovChain.Biallelic
