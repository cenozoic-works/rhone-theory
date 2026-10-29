/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! # The eight source offsets of the hierarchy recursion and the live-step count -/

@[expose] public section

namespace Rhone.LinearAlgebra.Propagation

open Finset

def steps : Finset (ℕ × ℕ) := {(2, 0), (1, 0), (0, 2), (0, 1), (2, 2), (2, 1), (1, 2), (1, 1)}

def live (α β : ℕ) : Finset (ℕ × ℕ) := steps.filter fun d => d.1 ≤ α ∧ d.2 ≤ β

theorem card_steps : steps.card = 8 := by decide

theorem mem_live {α β : ℕ} {d : ℕ × ℕ} : d ∈ live α β ↔ d ∈ steps ∧ d.1 ≤ α ∧ d.2 ≤ β :=
  mem_filter

theorem le_two_of_mem_steps {d : ℕ × ℕ} (hd : d ∈ steps) : d.1 ≤ 2 ∧ d.2 ≤ 2 := by
  fin_cases hd <;> exact ⟨by norm_num, by norm_num⟩

theorem live_eq_min (α β : ℕ) : live α β = live (min α 2) (min β 2) := by
  refine filter_congr fun d hd => ?_
  obtain ⟨h1, h2⟩ := le_two_of_mem_steps hd
  omega

theorem live_card_eq_one_iff_aux {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) :
    (live a b).card = 1 ↔ a + b = 1 := by
  interval_cases a <;> interval_cases b <;> decide

theorem live_card_eq_one_iff (α β : ℕ) : (live α β).card = 1 ↔ α + β = 1 := by
  rw [live_eq_min]
  rw [live_card_eq_one_iff_aux (min_le_right α 2) (min_le_right β 2)]
  omega

theorem live_card_eq_zero_iff (α β : ℕ) : (live α β).card = 0 ↔ α + β = 0 := by
  rw [live_eq_min, card_eq_zero]
  constructor
  · intro h
    by_contra hc
    have ha : min α 2 ≤ 2 := min_le_right α 2
    have hb : min β 2 ≤ 2 := min_le_right β 2
    have hc' : min α 2 + min β 2 ≠ 0 := by omega
    revert h hc'
    interval_cases (min α 2) <;> interval_cases (min β 2) <;> decide
  · intro h
    have : min α 2 = 0 := by omega
    have hb : min β 2 = 0 := by omega
    rw [this, hb]
    decide

theorem live_row_two {α : ℕ} (hα : 2 ≤ α) : live α 0 = {(2, 0), (1, 0)} := by
  rw [live_eq_min, min_eq_right hα, min_eq_left (by omega : (0 : ℕ) ≤ 2)]
  decide

theorem live_row_one : live 1 0 = {(1, 0)} := by decide

theorem live_col_one : live 0 1 = {(0, 1)} := by decide

theorem live_col_two {β : ℕ} (hβ : 2 ≤ β) : live 0 β = {(0, 2), (0, 1)} := by
  rw [live_eq_min, min_eq_right hβ, min_eq_left (by omega : (0 : ℕ) ≤ 2)]
  decide

theorem three_le_card_live {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) : 3 ≤ (live α β).card := by
  have hsub : ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)) ⊆ live α β := by
    intro d hd
    fin_cases hd <;> exact mem_live.2 ⟨by decide, by omega, by omega⟩
  calc (3 : ℕ) = ({(1, 0), (0, 1), (1, 1)} : Finset (ℕ × ℕ)).card := by decide
    _ ≤ (live α β).card := card_le_card hsub

end Rhone.LinearAlgebra.Propagation
