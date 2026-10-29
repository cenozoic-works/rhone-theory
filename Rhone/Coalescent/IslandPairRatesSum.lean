/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairRates

/-! # Labelled pair generator sums and holding rates -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset

theorem sum_distinct (d : Nat) (a : Fin d) (k : Real) :
    ∑ x : Fin d, (if a ≠ x then k else 0) = (d - 1 : Nat) * k := by
  have hterm : ∀ x : Fin d, (if a ≠ x then k else 0) =
      k - if a = x then k else 0 := by
    intro x
    by_cases h : a = x <;> simp [h]
  simp only [hterm, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [Nat.cast_sub (by have := a.isLt; omega), Nat.cast_one]
  ring

theorem eventRate_sum_mul (d : Nat) (m c : Real) (a b : Fin d)
    (f : State d → Real) :
    ∑ t, eventRate d m c (some (a,b)) t * f t =
      (if a = b then c else 0) * f none +
      destinationRate d m * (∑ x : Fin d, if a ≠ x then f (some (x,b)) else 0) +
      destinationRate d m * (∑ y : Fin d, if b ≠ y then f (some (a,y)) else 0) := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, eventRate, add_mul,
    sum_add_distrib]
  have hleft :
      (∑ x : Fin d, ∑ y : Fin d,
        (if b = y ∧ a ≠ x then destinationRate d m else 0) * f (some (x,y))) =
      destinationRate d m * (∑ x : Fin d, if a ≠ x then f (some (x,b)) else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    by_cases hax : a = x
    · simp [hax]
    · simp [hax]
  have hright :
      (∑ x : Fin d, ∑ y : Fin d,
        (if a = x ∧ b ≠ y then destinationRate d m else 0) * f (some (x,y))) =
      destinationRate d m * (∑ y : Fin d, if b ≠ y then f (some (a,y)) else 0) := by
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro y hy
    by_cases hby : b = y
    · simp [hby]
    · simp [hby]
  rw [hleft, hright]
  ring

theorem destinations_rate (d : Nat) (hd : 2 ≤ d) (m : Real) :
    (d - 1 : Nat) * destinationRate d m = m := by
  have h : ((d - 1 : Nat) : Real) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (show d - 1 ≠ 0 by omega)
  unfold destinationRate
  field_simp

theorem total_eventRate (d : Nat) (hd : 2 ≤ d) (m c : Real) (a b : Fin d) :
    ∑ t, eventRate d m c (some (a,b)) t = 2 * m + if a = b then c else 0 := by
  have h := eventRate_sum_mul d m c a b (fun _ => 1)
  simp only [mul_one] at h
  have hrate : destinationRate d m * (d - 1 : Nat) = m := by
    rw [mul_comm, destinations_rate d hd m]
  simp only [sum_distinct, mul_one, hrate] at h
  rw [h]
  ring

theorem rate_some (d : Nat) (hd : 2 ≤ d) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (a b : Fin d) :
    (chain d m c hm hc).rate (some (a,b)) = 2 * m + if a = b then c else 0 := by
  simp only [Rhone.MarkovChain.RateChain.rate, chain, generator, eventRate_self,
    ↓reduceIte, zero_sub, neg_neg]
  exact total_eventRate d hd m c a b

theorem generator_sum_mul (d : Nat) (m c : Real) (s : State d) (f : State d → Real) :
    ∑ t, generator d m c s t * f t =
      (∑ t, eventRate d m c s t * f t) - (∑ t, eventRate d m c s t) * f s := by
  simp only [generator, sub_mul, sum_sub_distrib]
  congr 1
  simp [ite_mul]

end Rhone.Coalescent.IslandPair
