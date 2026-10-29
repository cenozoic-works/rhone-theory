/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # The `ρ = 0` meet law, combinatorial core -/

@[expose] public section

namespace Rhone.MarkovChain.ClosedForms

structure MarkedTree (Leaf : Type*) (T : Type*) [LinearOrder T] [OrderBot T] where
  d : Leaf → Leaf → T
  fA : Leaf → T
  fB : Leaf → T
  d_self : ∀ i, d i i = ⊥
  d_comm : ∀ i j, d i j = d j i
  d_ultra : ∀ i j k, d i k ≤ max (d i j) (d j k)
  consistA : ∀ i j, d i j ≤ fA i → d i j ≤ fA j → fA i = fA j
  consistB : ∀ i j, d i j ≤ fB i → d i j ≤ fB j → fB i = fB j

namespace MarkedTree

variable {Leaf T : Type*} [LinearOrder T] [OrderBot T] (M : MarkedTree Leaf T)

def fStar (i : Leaf) : T := min (M.fA i) (M.fB i)

theorem fStar_eq_min (i : Leaf) : M.fStar i = min (M.fA i) (M.fB i) := rfl

def SameA (i j : Leaf) : Prop := M.d i j ≤ M.fA i ∧ M.d i j ≤ M.fA j

def SameB (i j : Leaf) : Prop := M.d i j ≤ M.fB i ∧ M.d i j ≤ M.fB j

def SameStar (i j : Leaf) : Prop := M.d i j ≤ M.fStar i ∧ M.d i j ≤ M.fStar j

theorem sameA_iff_first_eq (i j : Leaf) :
    M.SameA i j ↔ (M.d i j ≤ M.fA i ∧ M.fA i = M.fA j) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, M.consistA i j h1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 ▸ h1⟩

theorem sameA_refl (i : Leaf) : M.SameA i i := by
  constructor <;> · rw [M.d_self i]; exact bot_le

theorem sameA_symm {i j : Leaf} (h : M.SameA i j) : M.SameA j i := by
  rw [SameA, M.d_comm j i]
  exact ⟨h.2, h.1⟩

theorem sameA_trans {i j k : Leaf} (h₁ : M.SameA i j) (h₂ : M.SameA j k) : M.SameA i k := by
  have e₁ : M.fA i = M.fA j := M.consistA i j h₁.1 h₁.2
  have e₂ : M.fA j = M.fA k := M.consistA j k h₂.1 h₂.2
  have hik : M.d i k ≤ max (M.d i j) (M.d j k) := M.d_ultra i j k
  have hij : M.d i j ≤ M.fA i := h₁.1
  have hjk : M.d j k ≤ M.fA i := by rw [e₁]; exact h₂.1
  have hmax : max (M.d i j) (M.d j k) ≤ M.fA i := max_le hij hjk
  have h : M.d i k ≤ M.fA i := le_trans hik hmax
  exact ⟨h, by rw [e₁, e₂] at h; exact h⟩

theorem sameB_refl (i : Leaf) : M.SameB i i := by
  constructor <;> · rw [M.d_self i]; exact bot_le

theorem sameB_symm {i j : Leaf} (h : M.SameB i j) : M.SameB j i := by
  rw [SameB, M.d_comm j i]
  exact ⟨h.2, h.1⟩

theorem sameB_trans {i j k : Leaf} (h₁ : M.SameB i j) (h₂ : M.SameB j k) : M.SameB i k := by
  have e₁ : M.fB i = M.fB j := M.consistB i j h₁.1 h₁.2
  have e₂ : M.fB j = M.fB k := M.consistB j k h₂.1 h₂.2
  have hik : M.d i k ≤ max (M.d i j) (M.d j k) := M.d_ultra i j k
  have hij : M.d i j ≤ M.fB i := h₁.1
  have hjk : M.d j k ≤ M.fB i := by rw [e₁]; exact h₂.1
  have hmax : max (M.d i j) (M.d j k) ≤ M.fB i := max_le hij hjk
  have h : M.d i k ≤ M.fB i := le_trans hik hmax
  exact ⟨h, by rw [e₁, e₂] at h; exact h⟩

theorem sameStar_iff (i j : Leaf) : M.SameStar i j ↔ (M.SameA i j ∧ M.SameB i j) := by
  simp only [SameStar, SameA, SameB, fStar, le_min_iff]
  tauto

def setoidA : Setoid Leaf where
  r := M.SameA
  iseqv := ⟨M.sameA_refl, fun h => M.sameA_symm h, fun h₁ h₂ => M.sameA_trans h₁ h₂⟩

def setoidB : Setoid Leaf where
  r := M.SameB
  iseqv := ⟨M.sameB_refl, fun h => M.sameB_symm h, fun h₁ h₂ => M.sameB_trans h₁ h₂⟩

def setoidStar : Setoid Leaf where
  r := M.SameStar
  iseqv :=
    ⟨fun i => (M.sameStar_iff i i).mpr ⟨M.sameA_refl i, M.sameB_refl i⟩,
     fun {i j} h => (M.sameStar_iff j i).mpr
       ⟨M.sameA_symm ((M.sameStar_iff i j).mp h).1, M.sameB_symm ((M.sameStar_iff i j).mp h).2⟩,
     fun {i j k} h₁ h₂ => (M.sameStar_iff i k).mpr
       ⟨M.sameA_trans ((M.sameStar_iff i j).mp h₁).1 ((M.sameStar_iff j k).mp h₂).1,
        M.sameB_trans ((M.sameStar_iff i j).mp h₁).2 ((M.sameStar_iff j k).mp h₂).2⟩⟩

theorem setoidStar_eq_inf : M.setoidStar = M.setoidA ⊓ M.setoidB := by
  ext i j
  exact M.sameStar_iff i j

end MarkedTree

end Rhone.MarkovChain.ClosedForms
