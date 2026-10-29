/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.HouseOfCards

/-!
# Stationary second moments of the finite-effect quantitative house-of-cards law

Source: turelli1984, eq. (3.14), p. 152; barton_turelli1987, p. 161, eq. (3.8b). -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.HouseOfCards
open Finset

/-- Source: barton_turelli1987, p. 161, eq. (3.8b). -/
def effect {A : Type*} (a : A → ℝ) : Option A → ℝ
  | none => 0
  | some i => a i

/-- Source: turelli1984, eq. (3.14), p. 152; barton_turelli1987, p. 161, eq. (3.8b). -/
noncomputable def secondMoment {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) : ℝ :=
  ∑ i, equilibrium ν a S u i*(effect a i)^2

/-- Source: barton_turelli1987, p. 161, eq. (3.8b). -/
theorem selection_cost_ratio_bounds (a S : ℝ) (hS : 0 < S) (ha : a ≠ 0) :
    2*S ≤ a^2/(1-Real.exp (-a^2/(2*S))) ∧
      a^2/(1-Real.exp (-a^2/(2*S))) ≤ 2*S+a^2 := by
  let x := a^2/(2*S)
  have hx : 0 < x := div_pos (sq_pos_of_ne_zero ha) (by positivity)
  have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
  have hd : 0 < 1-Real.exp (-x) := sub_pos.mpr he
  have hl := Real.one_sub_le_exp_neg x
  have hu : (1+x)*Real.exp (-x) ≤ 1 := by
    calc
      _ ≤ Real.exp x*Real.exp (-x) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp x])
          (Real.exp_nonneg (-x))
      _ = 1 := by rw [← Real.exp_add]; simp
  have hax : a^2 = (2*S)*x := by dsimp [x]; field_simp
  have hneg : -a^2/(2*S) = -x := by dsimp [x]; ring
  rw [hneg]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    have hc : 0 ≤ (2*S)*((1+x)*(1-Real.exp (-x))-x) :=
      mul_nonneg (by positivity) (by nlinarith)
    nlinarith

/-- Source: turelli1984, eq. (3.14), p. 152; barton_turelli1987, p. 161, eq. (3.8b). -/
theorem stationary_second_moment_bounds {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ)
    (hν0 : ∀ i, 0 ≤ ν i) (hν : ∑ i, ν i = 1)
    (hS : 0 < S) (ha : ∀ i, a i ≠ 0) (hu : 0 ≤ u) :
    2*S*u ≤ secondMoment ν a S u ∧
      secondMoment ν a S u ≤ (2*S+∑ i, ν i*(a i)^2)*u := by
  have hm : secondMoment ν a S u =
      u*∑ i, ν i*((a i)^2/(1-Real.exp (-(a i)^2/(2*S)))) := by
    simp only [secondMoment, Fintype.sum_option, equilibrium, effect, pow_two,
      mul_zero, zero_add]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hm]
  have hlo : ∑ i, ν i*(2*S) ≤
      ∑ i, ν i*((a i)^2/(1-Real.exp (-(a i)^2/(2*S)))) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (selection_cost_ratio_bounds (a i) S hS (ha i)).1 (hν0 i)
  have hhi : (∑ i, ν i*((a i)^2/(1-Real.exp (-(a i)^2/(2*S))))) ≤
      ∑ i, ν i*(2*S+(a i)^2) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (selection_cost_ratio_bounds (a i) S hS (ha i)).2 (hν0 i)
  simp only [← sum_mul, hν, one_mul] at hlo
  simp only [mul_add, sum_add_distrib, ← sum_mul, hν, one_mul] at hhi
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hu]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hu]

end Rhone.MarkovChain.HouseOfCards
