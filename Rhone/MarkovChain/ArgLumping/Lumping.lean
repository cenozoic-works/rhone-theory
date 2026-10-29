/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Strong lumpability of a finite-state generator, and the pull-back of its potentials -/

@[expose] public section

namespace Rhone.MarkovChain.ArgLumping

open Finset

variable {α β K : Type*}

def fibre [Fintype α] [DecidableEq β] (Φ : α → β) (C : β) : Finset α :=
  Finset.univ.filter fun x => Φ x = C

@[simp] theorem mem_fibre [Fintype α] [DecidableEq β] {Φ : α → β} {C : β} {x : α} :
    x ∈ fibre Φ C ↔ Φ x = C := by
  simp [fibre]

def IsStrongLumping [Fintype α] [DecidableEq β] [CommRing K]
    (Q : Matrix α α K) (Φ : α → β) (Qbar : Matrix β β K) : Prop :=
  ∀ x : α, ∀ C : β, ∑ z ∈ fibre Φ C, Q x z = Qbar (Φ x) C

def IsLumpable [Fintype α] [DecidableEq β] [CommRing K] (Q : Matrix α α K) (Φ : α → β) : Prop :=
  ∀ x x' : α, Φ x = Φ x' → ∀ C : β, ∑ z ∈ fibre Φ C, Q x z = ∑ z ∈ fibre Φ C, Q x' z

theorem IsStrongLumping.isLumpable [Fintype α] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar) :
    IsLumpable Q Φ := by
  intro x x' hxx' C
  rw [h x C, h x' C, hxx']

theorem exists_lumped_of_isLumpable [Fintype α] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} (hΦ : Function.Surjective Φ) (h : IsLumpable Q Φ) :
    ∃ Qbar : Matrix β β K, IsStrongLumping Q Φ Qbar :=
  ⟨fun C C' => ∑ z ∈ fibre Φ C', Q (Function.surjInv hΦ C) z,
    fun x C => h x (Function.surjInv hΦ (Φ x)) (Function.surjInv_eq hΦ (Φ x)).symm C⟩

theorem isLumpable_iff [Fintype α] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} (hΦ : Function.Surjective Φ) :
    IsLumpable Q Φ ↔ ∃ Qbar : Matrix β β K, IsStrongLumping Q Φ Qbar :=
  ⟨exists_lumped_of_isLumpable hΦ, fun h => h.choose_spec.isLumpable⟩

def fib [DecidableEq β] [CommRing K] (Φ : α → β) : Matrix α β K :=
  fun x C => if Φ x = C then 1 else 0

theorem fib_mulVec [Fintype β] [DecidableEq β] [CommRing K] (Φ : α → β) (f : β → K) :
    (fib Φ : Matrix α β K).mulVec f = f ∘ Φ := by
  funext x
  simp [fib, Matrix.mulVec, dotProduct]

theorem mul_fib_apply [Fintype α] [DecidableEq β] [CommRing K] (Q : Matrix α α K) (Φ : α → β)
    (x : α) (C : β) : (Q * (fib Φ : Matrix α β K)) x C = ∑ z ∈ fibre Φ C, Q x z := by
  simp [Matrix.mul_apply, fib, fibre, Finset.sum_filter]

theorem fib_mul_apply [Fintype β] [DecidableEq β] [CommRing K] (Φ : α → β)
    (Qbar : Matrix β β K) (x : α) (C : β) :
    ((fib Φ : Matrix α β K) * Qbar) x C = Qbar (Φ x) C := by
  simp [Matrix.mul_apply, fib]

theorem lump_matrix_iff [Fintype α] [Fintype β] [DecidableEq β] [CommRing K]
    (Q : Matrix α α K) (Φ : α → β) (Qbar : Matrix β β K) :
    Q * (fib Φ : Matrix α β K) = (fib Φ : Matrix α β K) * Qbar ↔ IsStrongLumping Q Φ Qbar := by
  constructor
  · intro h x C
    have hxC := congrFun (congrFun h x) C
    rwa [mul_fib_apply, fib_mul_apply] at hxC
  · intro h
    ext x C
    rw [mul_fib_apply, fib_mul_apply]
    exact h x C

theorem lump_matrix [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar) :
    Q * (fib Φ : Matrix α β K) = (fib Φ : Matrix α β K) * Qbar :=
  (lump_matrix_iff Q Φ Qbar).2 h

theorem lump_of_matrix [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K}
    (h : Q * (fib Φ : Matrix α β K) = (fib Φ : Matrix α β K) * Qbar) :
    IsStrongLumping Q Φ Qbar :=
  (lump_matrix_iff Q Φ Qbar).1 h

theorem sum_row_lumped [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar) (x : α) :
    ∑ C, Qbar (Φ x) C = ∑ z, Q x z := by
  have hrow : ∀ C : β, Qbar (Φ x) C = ∑ z ∈ fibre Φ C, Q x z := fun C => (h x C).symm
  simp only [hrow, fibre]
  exact Finset.sum_fiberwise Finset.univ Φ (Q x)

theorem sum_row_lumped_eq_zero [Fintype α] [Fintype β] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar)
    (hΦ : Function.Surjective Φ) (hQ : ∀ x, ∑ z, Q x z = 0) (C : β) : ∑ C', Qbar C C' = 0 := by
  obtain ⟨x, rfl⟩ := hΦ C
  rw [sum_row_lumped h x, hQ x]

theorem isStrongLumping_of_offDiag [Fintype α] [Fintype β] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} {Qbar : Matrix β β K}
    (hoff : ∀ x : α, ∀ C : β, C ≠ Φ x → ∑ z ∈ fibre Φ C, Q x z = Qbar (Φ x) C)
    (hQ : ∀ x, ∑ z, Q x z = 0) (hQbar : ∀ C, ∑ C', Qbar C C' = 0) :
    IsStrongLumping Q Φ Qbar := by
  intro x C
  by_cases hC : C = Φ x
  · have e0 : ∑ D : β, (∑ z ∈ fibre Φ D, Q x z) = 0 := by
      simp only [fibre]
      rw [Finset.sum_fiberwise Finset.univ Φ (Q x)]
      exact hQ x
    have e1 := (Finset.add_sum_erase Finset.univ
      (fun D => ∑ z ∈ fibre Φ D, Q x z) (Finset.mem_univ C)).trans e0
    have e2 := (Finset.add_sum_erase Finset.univ (fun D => Qbar (Φ x) D)
      (Finset.mem_univ C)).trans (hQbar (Φ x))
    have e3 : ∑ D ∈ Finset.univ.erase C, ∑ z ∈ fibre Φ D, Q x z
        = ∑ D ∈ Finset.univ.erase C, Qbar (Φ x) D :=
      Finset.sum_congr rfl fun D hD =>
        hoff x D (by rw [← hC]; exact Finset.ne_of_mem_erase hD)
    rw [e3] at e1
    exact add_right_cancel (e1.trans e2.symm)
  · exact hoff x C hC

theorem mulVec_comp [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar) (ubar : β → K) :
    Q.mulVec (ubar ∘ Φ) = (Qbar.mulVec ubar) ∘ Φ := by
  rw [← fib_mulVec Φ ubar, Matrix.mulVec_mulVec, lump_matrix h, ← Matrix.mulVec_mulVec,
    fib_mulVec]

theorem pullback_exists [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar) {rbar ubar : β → K}
    (hu : Qbar.mulVec ubar = -rbar) : Q.mulVec (ubar ∘ Φ) = -(rbar ∘ Φ) := by
  rw [mulVec_comp h, hu]
  rfl

theorem pullback_of_lump [Fintype α] [Fintype β] [DecidableEq β] [CommRing K] {Q : Matrix α α K}
    {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar)
    (hQ : Function.Injective Q.mulVec) {rbar ubar : β → K} (hu : Qbar.mulVec ubar = -rbar)
    {u : α → K} (hu' : Q.mulVec u = -(rbar ∘ Φ)) : u = ubar ∘ Φ :=
  hQ (by rw [hu', pullback_exists h hu])

theorem injective_mulVec_lumped [Fintype α] [Fintype β] [DecidableEq β] [CommRing K]
    {Q : Matrix α α K} {Φ : α → β} {Qbar : Matrix β β K} (h : IsStrongLumping Q Φ Qbar)
    (hΦ : Function.Surjective Φ) (hQ : Function.Injective Q.mulVec) :
    Function.Injective Qbar.mulVec := by
  intro v w hvw
  have h2 : (v ∘ Φ) = (w ∘ Φ) := hQ (by rw [mulVec_comp h, mulVec_comp h, hvw])
  funext C
  obtain ⟨x, rfl⟩ := hΦ C
  exact congrFun h2 x

theorem pullback_w [CommRing K] {Φ : α → β} {rA rB uA uB : α → K}
    {rAbar rBbar uAbar uBbar : β → K} (hrA : rA = rAbar ∘ Φ) (hrB : rB = rBbar ∘ Φ)
    (huA : uA = uAbar ∘ Φ) (huB : uB = uBbar ∘ Φ) :
    (fun x => rA x * uB x + rB x * uA x)
      = (fun C => rAbar C * uBbar C + rBbar C * uAbar C) ∘ Φ := by
  subst hrA; subst hrB; subst huA; subst huB
  rfl

end Rhone.MarkovChain.ArgLumping
