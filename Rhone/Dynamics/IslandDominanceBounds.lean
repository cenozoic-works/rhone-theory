/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.DiploidSelection
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Continent-island selection with dominance: two-sided bounds on the equilibrium

Source: burger2013_migration_selection, sec. 4.4, eq. (4.37)–(4.42). -/

@[expose] public section

namespace Rhone.Dynamics

/-- Source: burger2013_migration_selection, sec. 4.4, eq. (4.37)–(4.42). -/
noncomputable def islandDomStep (h s m p : ℝ) : ℝ :=
  (1 - m) * selStep 1 (1 - h * s) (1 - s) p

theorem island_dom_fixed_quadratic {h s m p : ℝ} (hh1 : h ≤ 1) (hs1 : s ≤ 1)
    (hs0 : 0 < s) (hp0 : 0 < p) (hp1 : p < 1)
    (hfix : islandDomStep h s m p = p) :
    s * (1 - 2 * h) * (1 - p) ^ 2 + h * s * (1 + m) * (1 - p) = m := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hhs : h * s ≤ 1 := by nlinarith
  have hW : 0 < meanFit 1 (1 - h * s) (1 - s) p := by
    unfold meanFit
    have h1 : 0 ≤ 1 - h * s := by linarith
    have h2 : 0 ≤ 1 - s := by linarith
    have : 0 < p ^ 2 * 1 := by positivity
    have : 0 ≤ 2 * p * (1 - p) * (1 - h * s) := by positivity
    have : 0 ≤ (1 - p) ^ 2 * (1 - s) := by positivity
    linarith
  unfold islandDomStep selStep at hfix
  rw [← mul_div_assoc, div_eq_iff hW.ne'] at hfix
  have E : (1 - m) * (p + (1 - p) * (1 - h * s)) = meanFit 1 (1 - h * s) (1 - s) p := by
    apply mul_left_cancel₀ hp0.ne'
    unfold meanFit at hfix ⊢
    linear_combination hfix
  unfold meanFit at E
  linear_combination E

section Bounds

variable {h s m p : ℝ}

theorem island_dom_bounds_of_le_half (hh0 : 0 < h) (hh1 : h ≤ 1 / 2) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hm : 0 < m) (hp0 : 0 < p) (hp1 : p < 1)
    (hfix : islandDomStep h s m p = p) :
    m / (s * (1 - h + h * m)) ≤ 1 - p ∧ 1 - p ≤ m / (h * s * (1 + m)) := by
  have hQ := island_dom_fixed_quadratic (by linarith) hs1 hs0 hp0 hp1 hfix
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hc : 0 ≤ s * (1 - 2 * h) := mul_nonneg hs0.le (by linarith)
  have hd1 : 0 < s * (1 - h + h * m) := by
    have : 0 < 1 - h + h * m := by nlinarith
    positivity
  have hd2 : 0 < h * s * (1 + m) := by positivity
  constructor
  · rw [div_le_iff₀ hd1]
    nlinarith [mul_nonneg hc (mul_nonneg hq.le hp0.le)]
  · rw [le_div_iff₀ hd2]
    nlinarith [mul_nonneg hc (sq_nonneg (1 - p))]

theorem island_dom_bounds_of_half_le (hh0 : 1 / 2 ≤ h) (hh1 : h ≤ 1) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hm : 0 < m) (hp0 : 0 < p) (hp1 : p < 1)
    (hfix : islandDomStep h s m p = p) :
    m / (h * s * (1 + m)) ≤ 1 - p ∧ 1 - p ≤ m / (s * (1 - h + h * m)) := by
  have hhp : 0 < h := by linarith
  have hQ := island_dom_fixed_quadratic hh1 hs1 hs0 hp0 hp1 hfix
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hc : 0 ≤ s * (2 * h - 1) := mul_nonneg hs0.le (by linarith)
  have hd1 : 0 < s * (1 - h + h * m) := by
    have : 0 < 1 - h + h * m := by nlinarith
    positivity
  have hd2 : 0 < h * s * (1 + m) := by positivity
  constructor
  · rw [div_le_iff₀ hd2]
    nlinarith [mul_nonneg hc (sq_nonneg (1 - p))]
  · rw [le_div_iff₀ hd1]
    nlinarith [mul_nonneg hc (mul_nonneg hq.le hp0.le)]

end Bounds

end Rhone.Dynamics
