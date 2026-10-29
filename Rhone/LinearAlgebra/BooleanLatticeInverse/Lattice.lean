/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # The two shift operators of the Boolean lattice -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset

variable {F : Type*} [CommRing F] {i : ℕ}

def D : Module.End F (Finset (Fin i) → F) where
  toFun f S := ∑ x ∈ S, f (S.erase x)
  map_add' f g := by
    funext S
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp [Finset.mul_sum]

def U : Module.End F (Finset (Fin i) → F) where
  toFun f S := ∑ x ∈ Sᶜ, f (insert x S)
  map_add' f g := by
    funext S
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp [Finset.mul_sum]

theorem D_apply (f : Finset (Fin i) → F) (S : Finset (Fin i)) :
    D f S = ∑ x ∈ S, f (S.erase x) := rfl

theorem U_apply (f : Finset (Fin i) → F) (S : Finset (Fin i)) :
    U f S = ∑ x ∈ Sᶜ, f (insert x S) := rfl

def IsLevel (t : ℕ) (f : Finset (Fin i) → F) : Prop := ∀ S : Finset (Fin i), S.card ≠ t → f S = 0

def lev (t : ℕ) (f : Finset (Fin i) → F) : Finset (Fin i) → F :=
  fun S => if S.card = t then f S else 0

theorem lev_apply_of_card {t : ℕ} (f : Finset (Fin i) → F) {S : Finset (Fin i)}
    (h : S.card = t) : lev t f S = f S := ite_eq_left h

theorem isLevel_lev (t : ℕ) (f : Finset (Fin i) → F) : IsLevel t (lev t f) :=
  fun _ hS => ite_eq_right hS

theorem IsLevel.lev_eq {t : ℕ} {f : Finset (Fin i) → F} (h : IsLevel t f) : lev t f = f := by
  funext S
  by_cases hS : S.card = t
  · exact ite_eq_left hS
  · rw [lev, ite_eq_right hS, h S hS]

theorem IsLevel.ext {t : ℕ} {f g : Finset (Fin i) → F} (hf : IsLevel t f) (hg : IsLevel t g)
    (h : ∀ S : Finset (Fin i), S.card = t → f S = g S) : f = g := by
  funext S
  by_cases hS : S.card = t
  · exact h S hS
  · rw [hf S hS, hg S hS]

theorem isLevel_zero (t : ℕ) : IsLevel t (0 : Finset (Fin i) → F) := fun _ _ => rfl

theorem IsLevel.add {t : ℕ} {f g : Finset (Fin i) → F} (hf : IsLevel t f) (hg : IsLevel t g) :
    IsLevel t (f + g) := fun S hS => by
  rw [Pi.add_apply, hf S hS, hg S hS, add_zero]

theorem IsLevel.sub {t : ℕ} {f g : Finset (Fin i) → F} (hf : IsLevel t f) (hg : IsLevel t g) :
    IsLevel t (f - g) := fun S hS => by
  rw [Pi.sub_apply, hf S hS, hg S hS, sub_zero]

theorem IsLevel.smul {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) (c : F) :
    IsLevel t (c • f) := fun S hS => by
  rw [Pi.smul_apply, hf S hS, smul_zero]

theorem isLevel_sum {ι : Type*} {t : ℕ} (s : Finset ι) (f : ι → Finset (Fin i) → F)
    (h : ∀ a ∈ s, IsLevel t (f a)) : IsLevel t (∑ a ∈ s, f a) := fun S hS => by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha S hS

theorem IsLevel.eq_zero_of_lt {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) (ht : i < t) :
    f = 0 := by
  funext S
  refine hf S ?_
  have := Finset.card_le_univ S
  rw [Fintype.card_fin] at this
  omega

theorem IsLevel.map_D {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) :
    IsLevel (t + 1) (D f) := fun S hS => by
  rw [D_apply]
  refine Finset.sum_eq_zero fun x hx => hf _ ?_
  rw [Finset.card_erase_of_mem hx]
  have := Finset.card_pos.mpr ⟨x, hx⟩
  omega

theorem IsLevel.map_D_pow {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) (s : ℕ) :
    IsLevel (t + s) ((D ^ s) f) := by
  induction s with
  | zero => simpa using hf
  | succ s ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact ih.map_D

theorem IsLevel.map_U {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel (t + 1) f) :
    IsLevel t (U f) := fun S hS => by
  rw [U_apply]
  refine Finset.sum_eq_zero fun x hx => hf _ ?_
  rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hx)]
  omega

theorem IsLevel.U_eq_zero {f : Finset (Fin i) → F} (hf : IsLevel 0 f) : U f = 0 := by
  funext S
  rw [U_apply]
  refine Finset.sum_eq_zero fun x hx => hf _ ?_
  rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hx)]
  omega

theorem IsLevel.map_U_pow {t : ℕ} {f : Finset (Fin i) → F} (r : ℕ) (hf : IsLevel (t + r) f) :
    IsLevel t ((U ^ r) f) := by
  induction r generalizing t with
  | zero => simpa using hf
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (ih (t := t + 1) (by rwa [add_right_comm, add_assoc])).map_U

theorem IsLevel.U_pow_eq_zero {t r : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f)
    (h : t < r) : (U ^ r) f = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + t := ⟨r - 1 - t, by omega⟩
  have h0 : IsLevel 0 ((U ^ t) f) := IsLevel.map_U_pow t (by simpa using hf)
  rw [pow_add, Module.End.mul_apply, pow_succ, Module.End.mul_apply, h0.U_eq_zero, map_zero]

theorem U_D_sub_D_U_apply (f : Finset (Fin i) → F) (S : Finset (Fin i)) :
    U (D f) S - D (U f) S = ((i : F) - 2 * (S.card : F)) * f S := by
  have hDU : D (U f) S
      = (S.card : F) * f S + ∑ x ∈ S, ∑ y ∈ Sᶜ, f (insert y (S.erase x)) := by
    rw [D_apply]
    have : ∀ x ∈ S, U f (S.erase x) = f S + ∑ y ∈ Sᶜ, f (insert y (S.erase x)) := by
      intro x hx
      rw [U_apply, Finset.compl_erase,
        Finset.sum_insert (by simpa using hx), Finset.insert_erase hx]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hUD : U (D f) S
      = ((i : F) - (S.card : F)) * f S + ∑ x ∈ S, ∑ y ∈ Sᶜ, f (insert y (S.erase x)) := by
    rw [U_apply]
    have : ∀ y ∈ Sᶜ, D f (insert y S) = f S + ∑ x ∈ S, f (insert y (S.erase x)) := by
      intro y hy
      have hy' : y ∉ S := Finset.mem_compl.mp hy
      rw [D_apply, Finset.sum_insert hy', Finset.erase_insert hy']
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.erase_insert_of_ne (fun h => hy' (by rw [h]; exact hx))]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_comm, Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (by simpa using Finset.card_le_univ S)]
  rw [hDU, hUD]
  ring

theorem U_D_sub_D_U {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) :
    U (D f) = D (U f) + ((i : F) - 2 * (t : F)) • f := by
  funext S
  have h := U_D_sub_D_U_apply f S
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hS : S.card = t
  · rw [← hS]
    linear_combination h
  · rw [hf S hS] at h ⊢
    linear_combination h

theorem U_D_pow {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) (l : ℕ) :
    U ((D ^ (l + 1)) f)
      = (D ^ (l + 1)) (U f) + (((l : F) + 1) * ((i : F) - 2 * (t : F) - (l : F))) • (D ^ l) f := by
  induction l with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero,
      one_mul]
    exact U_D_sub_D_U hf
  | succ l ih =>
    rw [pow_succ' D (l + 1), Module.End.mul_apply, U_D_sub_D_U (hf.map_D_pow (l + 1)), ih, map_add,
      map_smul, Module.End.mul_apply, ← Module.End.mul_apply D (D ^ l) f, ← pow_succ',
      add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

def C : Module.End F (Finset (Fin i) → F) := LinearMap.funLeft F F compl

theorem C_apply (f : Finset (Fin i) → F) (S : Finset (Fin i)) : C f S = f Sᶜ := rfl

theorem C_C (f : Finset (Fin i) → F) : C (C f) = f := by
  funext S
  rw [C_apply, C_apply, compl_compl]

theorem C_D (f : Finset (Fin i) → F) : C (D f) = U (C f) := by
  funext S
  rw [C_apply, D_apply, U_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [C_apply, Finset.compl_insert]

theorem C_U (f : Finset (Fin i) → F) : C (U f) = D (C f) := by
  funext S
  rw [C_apply, D_apply, U_apply, compl_compl]
  exact Finset.sum_congr rfl fun x _ => by rw [C_apply, Finset.compl_erase]

theorem C_D_pow (s : ℕ) (f : Finset (Fin i) → F) : C ((D ^ s) f) = (U ^ s) (C f) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [pow_succ', Module.End.mul_apply, C_D, ih, pow_succ', Module.End.mul_apply]

theorem C_U_pow (s : ℕ) (f : Finset (Fin i) → F) : C ((U ^ s) f) = (D ^ s) (C f) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [pow_succ', Module.End.mul_apply, C_U, ih, pow_succ', Module.End.mul_apply]

theorem IsLevel.map_C {t : ℕ} {f : Finset (Fin i) → F} (hf : IsLevel t f) (ht : t ≤ i) :
    IsLevel (i - t) (C f) := fun S hS => by
  rw [C_apply]
  refine hf _ ?_
  have h := Finset.card_le_univ S
  rw [Fintype.card_fin] at h
  rw [Finset.card_compl, Fintype.card_fin]
  omega

end Rhone.LinearAlgebra.BooleanLatticeInverse
