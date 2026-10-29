/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairRatesSum
public import Mathlib.Tactic.LinearCombination

/-! # Same/different observable of the labelled island pair generator -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset

abbrev Category := Option Bool

def observe (d : Nat) : State d → Category
  | none => none
  | some (a,b) => if a = b then some true else some false

noncomputable def projectedGenerator (d : Nat) (m c : Real) : Category → Category → Real
  | none, _ => 0
  | some true, none => c
  | some true, some true => -(c + 2 * m)
  | some true, some false => 2 * m
  | some false, none => 0
  | some false, some true => 2 * destinationRate d m
  | some false, some false => -(2 * destinationRate d m)

theorem projectedGenerator_row_sum (d : Nat) (m c : Real) (s : Category) :
    ∑ t, projectedGenerator d m c s t = 0 := by
  cases s with
  | none => simp [projectedGenerator]
  | some b => cases b <;> simp [Fintype.sum_option, projectedGenerator]

private theorem sum_destination_observe (d : Nat) (a b : Fin d) (f : Category → Real) :
    (∑ x : Fin d, if a ≠ x then f (observe d (some (x,b))) else 0) =
      if a = b then (d - 1 : Nat) * f (some false)
      else (d - 1 : Nat) * f (some false) + f (some true) - f (some false) := by
  by_cases hab : a = b
  · subst b
    have hterm : ∀ x : Fin d,
        (if a ≠ x then f (observe d (some (x,a))) else 0) =
          if a ≠ x then f (some false) else 0 := by
      intro x
      by_cases hax : a = x
      · simp [hax]
      · simp [observe, hax, Ne.symm hax]
    simp only [hterm, sum_distinct, ↓reduceIte]
  · have hterm : ∀ x : Fin d,
        (if a ≠ x then f (observe d (some (x,b))) else 0) =
        (if a ≠ x then f (some false) else 0) +
          if x = b then f (some true) - f (some false) else 0 := by
      intro x
      by_cases hax : a = x
      · subst x; simp [hab]
      · by_cases hxb : x = b
        · subst x; simp [observe, hab]
        · simp [observe, hax, hxb]
    simp only [hterm, sum_add_distrib, sum_distinct, sum_ite_eq', mem_univ,
      ↓reduceIte, hab]
    ring

theorem generator_observe (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (s : State d) (f : Category → Real) :
    ∑ t, generator d m c s t * f (observe d t) =
      ∑ z, projectedGenerator d m c (observe d s) z * f z := by
  cases s with
  | none => simp [generator, eventRate, observe, projectedGenerator]
  | some p =>
    rcases p with ⟨a,b⟩
    rw [generator_sum_mul, eventRate_sum_mul, total_eventRate d hd]
    have hswap : (∑ y : Fin d, if b ≠ y then f (observe d (some (a,y))) else 0) =
        ∑ y : Fin d, if b ≠ y then f (observe d (some (y,a))) else 0 := by
      apply sum_congr rfl
      intro y hy
      simp only [observe, eq_comm]
    rw [hswap, sum_destination_observe, sum_destination_observe]
    have hk : destinationRate d m * (d - 1 : Nat) = m := by
      rw [mul_comm, destinations_rate d hd m]
    by_cases hab : a = b
    · simp only [observe, hab, ↓reduceIte, Fintype.sum_option,
        Fintype.sum_bool, projectedGenerator]
      linear_combination (2 * f (some false)) * hk
    · simp only [observe, hab, Ne.symm hab, ↓reduceIte, Fintype.sum_option,
        Fintype.sum_bool, projectedGenerator]
      linear_combination (2 * f (some false)) * hk

end Rhone.Coalescent.IslandPair
