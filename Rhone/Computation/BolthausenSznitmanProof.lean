/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.BolthausenSznitman
public import Rhone.Coalescent.LambdaRestriction
public import Mathlib.Basic.Real.Basic

/-!
# Executable Bolthausen-Sznitman rates equal the specification

Source: bolthausen_sznitman1998, Prop. 1.3, eq. (1.33). -/

@[expose] public section
namespace Rhone.Computation.BolthausenSznitman
open Finset MeasureTheory

theorem factorial_eq (n : Nat) : factorial n = Nat.factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.factorial_succ, ih]

theorem choose_eq (n k : Nat) : choose n k = Nat.choose n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih => cases k <;> simp [choose, Nat.choose_succ_succ, ih]

theorem mergeRate_eq {b k : Nat} (hk : 2 ≤ k) (hkb : k ≤ b) :
    ((mergeRate b k : Rat) : ℝ) =
      Rhone.Coalescent.lambdaRate (volume.restrict (Set.Icc 0 1)) b k := by
  rw [Rhone.Coalescent.lambdaRate_lebesgue hk hkb, mergeRate, factorial_eq, factorial_eq,
    factorial_eq]
  push_cast
  rfl

theorem partialTotal_eq (b : Nat) {m : Nat} (hm : m ≤ b) :
    ((partialTotal b m : Rat) : ℝ) = ∑ k ∈ Icc 2 m,
      (b.choose k : ℝ) * Rhone.Coalescent.lambdaRate (volume.restrict (Set.Icc 0 1)) b k := by
  induction m with
  | zero => simp [partialTotal]
  | succ m ih =>
    rw [partialTotal, Rat.cast_add, ih (by omega)]
    by_cases h : 2 ≤ m + 1
    · rw [Finset.sum_Icc_succ_top h]
      simp only [h, ↓reduceIte]
      rw [Rat.cast_mul, choose_eq, mergeRate_eq h hm]
      push_cast
      rfl
    · have : m + 1 = 1 := by omega
      have h0 : m = 0 := by omega
      subst h0
      simp

theorem totalRate_eq (b : Nat) (hb : 1 ≤ b) : totalRate b = (b : Rat) - 1 := by
  have h : ((totalRate b : Rat) : ℝ) = (((b : Rat) - 1 : Rat) : ℝ) := by
    rw [totalRate, partialTotal_eq b le_rfl,
      Rhone.Coalescent.sum_choose_mul_lambdaRate_lebesgue b hb]
    push_cast
    rfl
  exact_mod_cast h

theorem totalRate_eq_chain_rate {α : Type*} [Fintype α] [DecidableEq α]
    (π : Finpartition (univ : Finset α)) (hb : 1 ≤ π.parts.card) :
    ((totalRate π.parts.card : Rat) : ℝ) =
      (Rhone.Coalescent.bolthausenSznitmanChain α).rate π := by
  rw [Rhone.Coalescent.bolthausenSznitmanChain_rate, totalRate_eq _ hb]
  push_cast [Nat.cast_sub hb]
  rfl

example : totalRate 4 = 3 ∧ mergeRate 4 2 = 1 / 3 := by
  constructor
  · simp [totalRate, partialTotal, mergeRate, choose, factorial]; norm_num
  · simp [mergeRate, factorial]; norm_num

end Rhone.Computation.BolthausenSznitman
