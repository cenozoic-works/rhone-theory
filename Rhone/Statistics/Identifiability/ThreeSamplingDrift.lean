/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Tactic

/-! # Normalized occupancy algebra for arbitrary initial three-lineage sampling -/

@[expose] public section

namespace Rhone.Statistics.Identifiability.ThreeSampling

def xDrift (c q n x y : ℝ) : ℝ :=
  -c * x - 2 * c * y + 3 * c * x ^ 2 + 2 * q * (1 - n * x)

def yDrift (c q n x y : ℝ) : ℝ :=
  -3 * c * y * (1 - x) + 3 * q * (x - n * y)

lemma surface_derivative (c q n x : ℝ) :
    yDrift c q n x (x ^ 2) - 2 * x * xDrift c q n x (x ^ 2) =
      x * (q * (n * x - 1) - c * x * (1 - x)) := by
  unfold xDrift yDrift
  ring

lemma surface_balance (c q n x : ℝ) (hx : 0 < x)
    (hzero : yDrift c q n x (x ^ 2) - 2 * x * xDrift c q n x (x ^ 2) = 0) :
    q * (n * x - 1) = c * x * (1 - x) := by
  rw [surface_derivative] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hx))

lemma surface_drift (c q n x : ℝ)
    (hbalance : q * (n * x - 1) = c * x * (1 - x)) :
    xDrift c q n x (x ^ 2) = -3 * c * x * (1 - x) := by
  unfold xDrift
  nlinarith only [hbalance]

lemma surface_above_threshold (c q n x : ℝ) (hc : 0 < c) (hq : 0 ≤ q)
    (hn : 0 < n) (hx : 0 < x) (hx1 : x < 1)
    (hbalance : q * (n * x - 1) = c * x * (1 - x)) : 1 / n < x := by
  have hp : 0 < c * x * (1 - x) := mul_pos (mul_pos hc hx) (sub_pos.mpr hx1)
  have hnx : 0 < n * x - 1 := by
    by_contra h
    have he := mul_nonpos_of_nonneg_of_nonpos hq (le_of_not_gt h)
    linarith only [hbalance, hp, he]
  apply (div_lt_iff₀ hn).mpr
  nlinarith only [hnx]

theorem positivePart_drift_bound (c q n x y : ℝ)
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hn : 1 < n) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (htrace : 0 < c → y = x ^ 2 ∧
      yDrift c q n x y - 2 * x * xDrift c q n x y = 0) :
    (if 1 / n < x then xDrift c q n x y else 0) ≤ -3 * (c * x) * (1 - x) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  by_cases hc0 : c = 0
  · subst c
    split_ifs with h
    · unfold xDrift
      have hnx : 1 < n * x := by
        have hh := (div_lt_iff₀ hn0).mp h
        nlinarith only [hh]
      have hp := mul_nonpos_of_nonneg_of_nonpos hq (by linarith : 1 - n * x ≤ 0)
      nlinarith only [hp]
    · simp
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    obtain ⟨hy, hz⟩ := htrace hcpos
    subst y
    by_cases hx0 : x = 0
    · subst x
      have ht : ¬ 1 / n < (0 : ℝ) := not_lt_of_ge (div_nonneg zero_le_one hn0.le)
      rw [ite_eq_right ht]
      simp only [mul_zero, sub_zero, zero_mul, le_refl]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hb := surface_balance c q n x hxpos hz
      have ht : 1 / n < x := by
        rcases lt_or_eq_of_le hx1 with hlt | heq
        · exact surface_above_threshold c q n x hcpos hq hn0 hxpos hlt hb
        · rw [heq]
          exact (div_lt_one hn0).mpr hn
      rw [ite_eq_left ht, surface_drift c q n x hb]
      ring_nf
      exact le_rfl

end Rhone.Statistics.Identifiability.ThreeSampling
