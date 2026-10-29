/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Stepwise mutation on a finite cycle and the integer line

Source: ewens1979, sec. 9.5, pp. 258–259. -/

@[expose] public section
namespace Rhone.Dynamics.MutationModels
open Finset

noncomputable def integerStepwise (u : ℝ) (i j : ℤ) : ℝ :=
  (if j = i then 1 - u else 0) +
  (if j = i - 1 then u / 2 else 0) + (if j = i + 1 then u / 2 else 0)

noncomputable def cycleStepwise (K : ℕ) (u : ℝ)
    (i j : ZMod (K + 3)) : ℝ :=
  (if j = i then 1 - u else 0) +
  (if j = i - 1 then u / 2 else 0) + (if j = i + 1 then u / 2 else 0)

noncomputable def cycleUniform (K : ℕ) (_i : ZMod (K + 3)) : ℝ := 1 / (K + 3)

theorem cycle_markov (K : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∀ i j, 0 ≤ cycleStepwise K u i j) ∧
    (∀ i, ∑ j, cycleStepwise K u i j = 1) := by
  constructor
  · intro i j
    unfold cycleStepwise
    have hstay : 0 ≤ 1 - u := sub_nonneg.mpr hu1
    positivity
  · intro i
    simp only [cycleStepwise, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    ring

theorem cycle_uniform_probability (K : ℕ) :
    (∀ i, 0 ≤ cycleUniform K i) ∧ ∑ i, cycleUniform K i = 1 := by
  constructor
  · intro i; unfold cycleUniform; positivity
  · simp only [cycleUniform, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_ofNat]
    field_simp

theorem cycle_reversible (K : ℕ) (u : ℝ) (i j : ZMod (K + 3)) :
    cycleUniform K i * cycleStepwise K u i j =
      cycleUniform K j * cycleStepwise K u j i := by
  have hm : j = i - 1 ↔ i = j + 1 := by
    constructor <;> intro h <;> linear_combination -h
  have hp : j = i + 1 ↔ i = j - 1 := by
    constructor <;> intro h <;> linear_combination -h
  unfold cycleUniform cycleStepwise
  simp only [hm, hp, eq_comm (a := j) (b := i)]
  ring

theorem cycle_stationary (K : ℕ) (u : ℝ) (j : ZMod (K + 3)) :
    ∑ i, cycleUniform K i * cycleStepwise K u i j = cycleUniform K j := by
  simp_rw [cycle_reversible]
  simp [cycleStepwise, cycleUniform, mul_add, sum_add_distrib]
  ring

theorem integer_harmonic_nonneg_constant (p : ℤ → ℝ)
    (hp : ∀ n, 0 ≤ p n)
    (hbalance : ∀ n, 2 * p n = p (n - 1) + p (n + 1)) :
    ∀ n, p n = p 0 := by
  have hd (n : ℤ) : p (n + 1) - p n = p 1 - p 0 := by
    induction n using Int.induction_on with
    | zero => norm_num
    | succ n ih =>
      have hb := hbalance (n + 1)
      have he : (n:ℤ) + 1 - 1 = (n:ℤ) := by ring
      rw [he] at hb
      linarith
    | pred n ih =>
      have hb := hbalance (-(n:ℤ))
      have he : -(n:ℤ) - 1 + 1=-(n:ℤ) := by ring
      rw [he]
      linarith
  have ha (n : ℤ) : p n = p 0 + (n:ℝ) * (p 1 - p 0) := by
    induction n using Int.induction_on with
    | zero => norm_num
    | succ n ih =>
      have hh := hd n
      push_cast at ih ⊢
      linarith
    | pred n ih =>
      have hh := hd (-(n:ℤ) - 1)
      have he : -(n:ℤ) - 1 + 1=-(n:ℤ) := by ring
      rw [he] at hh
      push_cast at ih ⊢
      linarith
  have hc : p 1 - p 0 = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg | hpos
    · obtain ⟨n, hn⟩ := exists_nat_gt (p 0 / (-(p 1 - p 0)))
      have hn' : p 0 < (n:ℝ) * (-(p 1 - p 0)) :=
        (div_lt_iff₀ (neg_pos.mpr hneg)).mp hn
      have hn0 := hp (n:ℤ)
      rw [ha] at hn0
      norm_cast at hn0
      nlinarith
    · obtain ⟨n, hn⟩ := exists_nat_gt (p 0 / (p 1 - p 0))
      have hn' : p 0 < (n:ℝ) * (p 1 - p 0) := (div_lt_iff₀ hpos).mp hn
      have hn0 := hp (-(n:ℤ))
      rw [ha] at hn0
      push_cast at hn0
      nlinarith
  intro n
  rw [ha, hc, mul_zero, add_zero]

theorem integer_stepwise_no_stationary (u : ℝ) (hu : 0 < u)
    (p : ℤ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (hbalance : ∀ n, p n = (1 - u) * p n + (u / 2) * p (n - 1) + (u / 2) * p (n + 1)) :
    False := by
  have hb (n : ℤ) : 2 * p n = p (n - 1) + p (n + 1) := by
    have h := hbalance n
    nlinarith
  have hc := integer_harmonic_nonneg_constant p hp hb
  have he : p = fun _ => p 0 := funext hc
  rw [he] at hsum
  have hz : p 0 = 0 := by
    exact (summable_const_iff (p 0)).mp hsum.summable
  rw [hz] at hsum
  have h01 : (0:ℝ) = 1 := hasSum_zero.unique hsum
  norm_num at h01

theorem integer_stepwise_stochastic (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∀ i j, 0 ≤ integerStepwise u i j) ∧
    (∀ i, HasSum (integerStepwise u i) 1) := by
  constructor
  · intro i j
    unfold integerStepwise
    have hstay : 0 ≤ 1 - u := sub_nonneg.mpr hu1
    positivity
  · intro i
    convert ((hasSum_ite_eq i (1 - u)).add
      (hasSum_ite_eq (i - 1) (u / 2))).add (hasSum_ite_eq (i + 1) (u / 2)) using 1
    · rfl
    · ring

theorem integer_stepwise_symmetric (u : ℝ) (i j : ℤ) :
    integerStepwise u i j = integerStepwise u j i := by
  have hm : j = i - 1 ↔ i = j + 1 := by omega
  have hp : j = i + 1 ↔ i = j - 1 := by omega
  unfold integerStepwise
  simp only [hm, hp, eq_comm (a := j) (b := i)]
  ring

theorem integer_stepwise_inflow (u : ℝ) (p : ℤ → ℝ) (n : ℤ) :
    (∑' i, p i * integerStepwise u i n) =
      (1 - u) * p n + (u / 2) * p (n - 1) + (u / 2) * p (n + 1) := by
  have hterm (a : ℤ) (c : ℝ) :
      HasSum (fun i => p i * (if i = a then c else 0)) (c * p a) := by
    convert hasSum_ite_eq a (c * p a) using 1
    funext i
    split_ifs with h
    · subst i; ring
    · ring
  have h := ((hterm n (1 - u)).add (hterm (n - 1) (u / 2))).add
    (hterm (n + 1) (u / 2))
  have he (i : ℤ) : p i * integerStepwise u i n =
      p i * (if i = n then 1 - u else 0) +
      p i * (if i = n - 1 then u / 2 else 0) +
      p i * (if i = n + 1 then u / 2 else 0) := by
    rw [integer_stepwise_symmetric]
    unfold integerStepwise
    ring
  simp_rw [he]
  exact h.tsum_eq

end Rhone.Dynamics.MutationModels
