/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairRatesSum

/-! # Exact candidate times solve the labelled island pair generator equation -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset

noncomputable def sameTime (d : Nat) (c : Real) : Real := d / c

noncomputable def differentTime (d : Nat) (m c : Real) : Real :=
  sameTime d c + (d - 1 : Nat) / (2 * m)

noncomputable def meanTime (d : Nat) (m c : Real) : State d → Real
  | none => 0
  | some (a,b) => if a = b then sameTime d c else differentTime d m c

theorem meanTime_swap (d : Nat) (m c : Real) (a b : Fin d) :
    meanTime d m c (some (a,b)) = meanTime d m c (some (b,a)) := by
  simp only [meanTime, eq_comm]

theorem sum_destination_mean (d : Nat) (m c : Real) (a b : Fin d) :
    (∑ x : Fin d, if a ≠ x then meanTime d m c (some (x,b)) else 0) =
      if a = b then (d - 1 : Nat) * differentTime d m c
      else (d - 1 : Nat) * differentTime d m c + sameTime d c - differentTime d m c := by
  by_cases hab : a = b
  · subst b
    have hterm : ∀ x : Fin d,
        (if a ≠ x then meanTime d m c (some (x,a)) else 0) =
        if a ≠ x then differentTime d m c else 0 := by
      intro x
      by_cases hax : a = x
      · simp [hax]
      · simp [meanTime, hax, Ne.symm hax]
    simp only [hterm, sum_distinct, ↓reduceIte]
  · have hterm : ∀ x : Fin d,
        (if a ≠ x then meanTime d m c (some (x,b)) else 0) =
        (if a ≠ x then differentTime d m c else 0) +
          if x = b then sameTime d c - differentTime d m c else 0 := by
      intro x
      by_cases hax : a = x
      · subst x; simp [hab]
      · by_cases hxb : x = b
        · subst x; simp [meanTime, hab]
        · simp [meanTime, hax, hxb]
    simp only [hterm, sum_add_distrib, sum_distinct, sum_ite_eq', mem_univ,
      ↓reduceIte, hab]
    ring

theorem meanTime_generator (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) :
    ∑ t, generator d m c (some (a,b)) t * meanTime d m c t = -1 := by
  rw [generator_sum_mul, eventRate_sum_mul, total_eventRate d hd]
  simp only [show meanTime d m c none = 0 from rfl, mul_zero, zero_add]
  have hswap :
      (∑ y : Fin d, if b ≠ y then meanTime d m c (some (a,y)) else 0) =
      ∑ y : Fin d, if b ≠ y then meanTime d m c (some (y,a)) else 0 := by
    apply sum_congr rfl
    intro y hy
    rw [meanTime_swap d m c a y]
  rw [hswap, sum_destination_mean, sum_destination_mean]
  have hn : ((d - 1 : Nat) : Real) = (d : Real) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hn0 : ((d - 1 : Nat) : Real) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (show d - 1 ≠ 0 by omega)
  have hr : (d : Real) - 1 ≠ 0 := by rw [← hn]; exact hn0
  by_cases hab : a = b
  · simp only [meanTime, hab, ↓reduceIte, differentTime,
      sameTime, destinationRate, hn]
    field_simp [ne_of_gt hm, ne_of_gt hc, hr]
    ring
  · simp only [meanTime, hab, Ne.symm hab, ↓reduceIte, differentTime,
      sameTime, destinationRate, hn]
    field_simp [ne_of_gt hm, ne_of_gt hc, hr]
    ring

end Rhone.Coalescent.IslandPair
