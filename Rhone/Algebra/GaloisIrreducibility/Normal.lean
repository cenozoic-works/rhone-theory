/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-! # A nontrivial normal subgroup of `S_m` is transitive -/

@[expose] public section

namespace Rhone.Algebra.GaloisIrreducibility

open Equiv

variable {α : Type*}

theorem exists_perm_pair {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ τ : Equiv.Perm α, τ a = c ∧ τ b = d := by
  classical
  have hb : Equiv.swap a c b ≠ c := by
    intro h
    have h' : Equiv.swap a c b = Equiv.swap a c a := by rw [h, Equiv.swap_apply_left]
    exact hab (((Equiv.swap a c).injective h').symm)
  refine ⟨Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hb) hcd
  · rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _

theorem exists_mem_ne_one {N : Subgroup (Equiv.Perm α)} (hne : N ≠ ⊥) :
    ∃ σ ∈ N, ∃ a : α, σ a ≠ a := by
  by_contra hcon
  refine hne (Subgroup.eq_bot_iff_forall N |>.mpr fun σ hσ => ?_)
  refine Equiv.ext fun x => ?_
  by_contra hx
  exact hcon ⟨σ, hσ, x, hx⟩

theorem exists_mem_apply_eq {N : Subgroup (Equiv.Perm α)} [hN : N.Normal] (hne : N ≠ ⊥)
    (c d : α) : ∃ σ ∈ N, σ c = d := by
  classical
  rcases eq_or_ne c d with rfl | hcd
  · exact ⟨1, N.one_mem, rfl⟩
  · obtain ⟨σ, hσN, a, ha⟩ := exists_mem_ne_one hne
    obtain ⟨τ, hτa, hτb⟩ := exists_perm_pair (Ne.symm ha) hcd
    refine ⟨τ * σ * τ⁻¹, hN.conj_mem σ hσN τ, ?_⟩
    have h1 : τ⁻¹ c = a := by rw [← hτa]; simp
    simp only [Equiv.Perm.mul_apply, h1, hτb]

theorem isPretransitive_of_normal {N : Subgroup (Equiv.Perm α)} [N.Normal] (hne : N ≠ ⊥) :
    MulAction.IsPretransitive N α := by
  classical
  refine ⟨fun c d => ?_⟩
  obtain ⟨σ, hσ, h⟩ := exists_mem_apply_eq hne c d
  exact ⟨⟨σ, hσ⟩, h⟩

theorem eq_bot_or_transitive (N : Subgroup (Equiv.Perm α)) [N.Normal] :
    N = ⊥ ∨ ∀ c d : α, ∃ σ ∈ N, σ c = d := by
  classical
  rcases eq_or_ne N ⊥ with h | h
  · exact Or.inl h
  · exact Or.inr fun c d => exists_mem_apply_eq h c d

theorem eq_bot_of_not_transitive {N : Subgroup (Equiv.Perm α)} [N.Normal]
    (h : ¬ ∀ c d : α, ∃ σ ∈ N, σ c = d) : N = ⊥ :=
  (eq_bot_or_transitive N).resolve_right h

end Rhone.Algebra.GaloisIrreducibility
