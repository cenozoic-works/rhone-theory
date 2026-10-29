/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateChain
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sum

/-!
# The structured coalescent for `n` lineages in `d` demes

Source: notohara1990, sec. 2; sampson2006, sec. 2, eq. (2.2). -/

@[expose] public section

namespace Rhone.Coalescent.Structured

open Finset

variable {n d : ℕ}

abbrev State (n d : ℕ) := Fin n → Fin n ⊕ Fin d

def MigAdj (M : Fin d → Fin d → ℝ) (a b : Fin d) : Prop := a ≠ b ∧ 0 < M a b

def MigIrreducible (M : Fin d → Fin d → ℝ) : Prop :=
  ∀ a b, Relation.ReflTransGen (MigAdj M) a b

def migrate (x : State n d) (i : Fin n) (b : Fin d) : State n d :=
  Function.update x i (Sum.inr b)

def merge (x : State n d) (i j : Fin n) : State n d :=
  fun k => if k = j ∨ x k = Sum.inl j then Sum.inl i else x k

noncomputable def eventRate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x y : State n d) : ℝ :=
  (∑ i, ∑ a, ∑ b, if (x i = Sum.inr a ∧ a ≠ b) ∧ y = migrate x i b then M a b else 0) +
  ∑ i, ∑ j, ∑ a,
    if (i < j ∧ x i = Sum.inr a ∧ x j = Sum.inr a) ∧ y = merge x i j then c a else 0

noncomputable def generator (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x y : State n d) : ℝ :=
  eventRate M c x y - if x = y then ∑ z, eventRate M c x z else 0

theorem migrate_apply_self (x : State n d) (i : Fin n) (b : Fin d) :
    migrate x i b i = Sum.inr b := by
  simp [migrate]

theorem migrate_apply_of_ne (x : State n d) {i k : Fin n} (h : k ≠ i) (b : Fin d) :
    migrate x i b k = x k := by
  simp [migrate, h]

theorem merge_apply_self (x : State n d) (i j : Fin n) : merge x i j j = Sum.inl i := by
  simp [merge]

theorem merge_apply_of_inr (x : State n d) (i : Fin n) {j k : Fin n} {a : Fin d}
    (hk : x k = Sum.inr a) (hkj : k ≠ j) : merge x i j k = Sum.inr a := by
  simp [merge, hk, hkj]

theorem migrate_ne (x : State n d) {i : Fin n} {a b : Fin d} (hi : x i = Sum.inr a)
    (hab : a ≠ b) : x ≠ migrate x i b := by
  intro h
  have h1 := congrFun h i
  rw [migrate_apply_self, hi] at h1
  exact hab (Sum.inr.inj h1)

theorem merge_ne (x : State n d) (i : Fin n) {j : Fin n} {a : Fin d} (hj : x j = Sum.inr a) :
    x ≠ merge x i j := by
  intro h
  have h1 := congrFun h j
  rw [merge_apply_self, hj] at h1
  exact Sum.inr_ne_inl h1

private theorem migrate_inj (x : State n d) {i i' : Fin n} {a' b b' : Fin d}
    (hi' : x i' = Sum.inr a') (hab' : a' ≠ b') (h : migrate x i b = migrate x i' b') :
    i' = i ∧ b' = b := by
  by_cases hii : i' = i
  · subst hii
    have h1 := congrFun h i'
    rw [migrate_apply_self, migrate_apply_self] at h1
    exact ⟨rfl, (Sum.inr.inj h1).symm⟩
  · have h1 := congrFun h i'
    rw [migrate_apply_self, migrate_apply_of_ne x hii, hi'] at h1
    exact absurd (Sum.inr.inj h1) hab'

private theorem migrate_ne_merge (x : State n d) (i : Fin n) (b : Fin d) (i' : Fin n)
    {j : Fin n} {a : Fin d} (hj : x j = Sum.inr a) : migrate x i b ≠ merge x i' j := by
  intro h
  have h1 := congrFun h j
  rw [merge_apply_self] at h1
  by_cases hji : j = i
  · subst hji
    rw [migrate_apply_self] at h1
    exact Sum.inr_ne_inl h1
  · rw [migrate_apply_of_ne x hji, hj] at h1
    exact Sum.inr_ne_inl h1

private theorem merge_inj (x : State n d) {i j i' j' : Fin n} {a' : Fin d}
    (hj' : x j' = Sum.inr a') (h : merge x i j = merge x i' j') : i' = i ∧ j' = j := by
  have h1 := congrFun h j'
  rw [merge_apply_self] at h1
  by_cases hjj : j' = j
  · subst hjj
    rw [merge_apply_self] at h1
    exact ⟨(Sum.inl.inj h1).symm, rfl⟩
  · rw [merge_apply_of_inr x i hj' hjj] at h1
    exact absurd h1 Sum.inr_ne_inl

theorem exists_event_of_eventRate_ne_zero (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    {x y : State n d} (h : eventRate M c x y ≠ 0) :
    (∃ i a b, x i = Sum.inr a ∧ a ≠ b ∧ y = migrate x i b) ∨
      ∃ i j a, i < j ∧ x i = Sum.inr a ∧ x j = Sum.inr a ∧ y = merge x i j := by
  by_contra hcon
  rw [not_or] at hcon
  apply h
  unfold eventRate
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · exact fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ =>
      ite_eq_right fun hh => hcon.2 ⟨i, j, a, hh.1.1, hh.1.2.1, hh.1.2.2, hh.2⟩
  · exact fun i _ => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      ite_eq_right fun hh => hcon.1 ⟨i, a, b, hh.1.1, hh.1.2, hh.2⟩

theorem eventRate_self (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d) :
    eventRate M c x x = 0 := by
  by_contra h
  rcases exists_event_of_eventRate_ne_zero M c h with ⟨i, a, b, hi, hab, hx⟩ |
    ⟨i, j, a, -, -, hj, hx⟩
  · exact migrate_ne x hi hab hx
  · exact merge_ne x i hj hx

theorem eventRate_nonneg (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x y : State n d) :
    0 ≤ eventRate M c x y := by
  refine add_nonneg ?_ ?_
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg
      fun b _ => ?_
    split_ifs with h
    · exact hM a b h.1.2
    · exact le_rfl
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg
      fun a _ => ?_
    split_ifs with h
    · exact hc a
    · exact le_rfl

theorem generator_row_sum (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d) :
    ∑ y, generator M c x y = 0 := by
  simp [generator, Finset.sum_sub_distrib]

noncomputable def chain (n : ℕ) {d : ℕ} (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) : Rhone.MarkovChain.RateChain (State n d)
        where
  Q := generator M c
  off_diag_nonneg x y hxy := by
    simp only [generator, hxy, ↓reduceIte, sub_zero]
    exact eventRate_nonneg M c hM hc x y
  row_sum := generator_row_sum M c

theorem eventRate_migrate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d) {i : Fin n}
    {a b : Fin d} (hi : x i = Sum.inr a) (hab : a ≠ b) :
    eventRate M c x (migrate x i b) = M a b := by
  unfold eventRate
  have h2 : (∑ i', ∑ j', ∑ a', if (i' < j' ∧ x i' = Sum.inr a' ∧ x j' = Sum.inr a') ∧
      migrate x i b = merge x i' j' then c a' else 0) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero
      fun a' _ => ite_eq_right fun hh => migrate_ne_merge x i b i' hh.1.2.2 hh.2
  rw [h2, add_zero, Finset.sum_eq_single i, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [hi, hab]
  · exact fun b' _ hb' => ite_eq_right fun hh => hb' (migrate_inj x hh.1.1 hh.1.2 hh.2).2
  · exact fun h => absurd (mem_univ b) h
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun b' _ => ite_eq_right fun hh => ha' ?_
    exact (Sum.inr.inj (hi.symm.trans hh.1.1)).symm
  · exact fun h => absurd (mem_univ a) h
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ =>
      ite_eq_right fun hh => hi' (migrate_inj x hh.1.1 hh.1.2 hh.2).1
  · exact fun h => absurd (mem_univ i) h

theorem eventRate_merge (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d) {i j : Fin n}
    {a : Fin d} (hij : i < j) (hi : x i = Sum.inr a) (hj : x j = Sum.inr a) :
    eventRate M c x (merge x i j) = c a := by
  unfold eventRate
  have h1 : (∑ i', ∑ a', ∑ b', if (x i' = Sum.inr a' ∧ a' ≠ b') ∧
      merge x i j = migrate x i' b' then M a' b' else 0) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero
      fun b' _ => ite_eq_right fun hh => migrate_ne_merge x i' b' i hj hh.2.symm
  rw [h1, zero_add, Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single a]
  · simp [hi, hj, hij]
  · intro a' _ ha'
    exact ite_eq_right fun hh => ha' (Sum.inr.inj (hi.symm.trans hh.1.2.1)).symm
  · exact fun h => absurd (mem_univ a) h
  · intro j' _ hj'
    exact Finset.sum_eq_zero fun a' _ => ite_eq_right fun hh => hj' (merge_inj x hh.1.2.2 hh.2).2
  · exact fun h => absurd (mem_univ j) h
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun a' _ =>
      ite_eq_right fun hh => hi' (merge_inj x hh.1.2.2 hh.2).1
  · exact fun h => absurd (mem_univ i) h

theorem chain_Q_migrate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) {i : Fin n}
    {a b : Fin d} (hi : x i = Sum.inr a) (hab : a ≠ b) :
    (chain n M c hM hc).Q x (migrate x i b) = M a b := by
  change generator M c x (migrate x i b) = M a b
  rw [generator, ite_eq_right (migrate_ne x hi hab), sub_zero, eventRate_migrate M c x hi hab]

theorem chain_Q_merge (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) {i j : Fin n}
    {a : Fin d} (hij : i < j) (hi : x i = Sum.inr a) (hj : x j = Sum.inr a) :
    (chain n M c hM hc).Q x (merge x i j) = c a := by
  change generator M c x (merge x i j) = c a
  rw [generator, ite_eq_right (merge_ne x i hj), sub_zero, eventRate_merge M c x hij hi hj]

private theorem sum_ite_and_eq_mul {α : Type*} [Fintype α] [DecidableEq α] (P : Prop)
    [Decidable P] (t : α) (r : ℝ) (g : α → ℝ) :
    ∑ y, (if P ∧ y = t then r else 0) * g y = if P then r * g t else 0 := by
  by_cases hP : P <;> simp [hP]

private theorem sum_eventRate_mul (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d)
    (g : State n d → ℝ) :
    ∑ y, eventRate M c x y * g y =
      (∑ i, ∑ a, ∑ b, if x i = Sum.inr a ∧ a ≠ b then M a b * g (migrate x i b) else 0) +
      ∑ i, ∑ j, ∑ a,
        if i < j ∧ x i = Sum.inr a ∧ x j = Sum.inr a then c a * g (merge x i j) else 0 := by
  simp only [eventRate, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => sum_ite_and_eq_mul _ _ _ g
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => sum_ite_and_eq_mul _ _ _ g

theorem sum_generator_mul (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (x : State n d)
    (g : State n d → ℝ) :
    ∑ y, generator M c x y * g y =
      (∑ i, ∑ a, ∑ b,
        if x i = Sum.inr a ∧ a ≠ b then M a b * (g (migrate x i b) - g x) else 0) +
      ∑ i, ∑ j, ∑ a,
        if i < j ∧ x i = Sum.inr a ∧ x j = Sum.inr a then c a * (g (merge x i j) - g x)
        else 0 := by
  have h0 : ∑ y, generator M c x y * g y =
      (∑ y, eventRate M c x y * g y) - (∑ y, eventRate M c x y) * g x := by
    simp only [generator, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [ite_mul]
  have h1 := sum_eventRate_mul M c x fun _ => 1
  simp only [mul_one] at h1
  rw [h0, sum_eventRate_mul, h1, add_mul, add_sub_add_comm]
  congr 1
  · simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  · simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring

theorem rate_eq (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) :
    (chain n M c hM hc).rate x =
      (∑ i, ∑ a, ∑ b, if x i = Sum.inr a ∧ a ≠ b then M a b else 0) +
      ∑ i, ∑ j, ∑ a, if i < j ∧ x i = Sum.inr a ∧ x j = Sum.inr a then c a else 0 := by
  have h1 := sum_eventRate_mul M c x fun _ => 1
  simp only [mul_one] at h1
  rw [← h1]
  simp [Rhone.MarkovChain.RateChain.rate, chain, generator, eventRate_self]

end Rhone.Coalescent.Structured
