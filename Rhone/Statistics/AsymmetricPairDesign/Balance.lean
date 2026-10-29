/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! # Algebraic balance inequalities for the asymmetric Laplace potentials -/

@[expose] public section

namespace Rhone.Statistics.AsymmetricPairDesign

theorem balance_separation {a b k x y z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hk : 0 < k) (hy : 0 < y) (h : (k + a + b) * y = b * x + a * z) :
    y < x ∨ y < z := by
  by_contra hn
  have hxy : x ≤ y := le_of_not_gt (fun hxy => hn (Or.inl hxy))
  have hzy : z ≤ y := le_of_not_gt (fun hzy => hn (Or.inr hzy))
  have hx := mul_le_mul_of_nonneg_left hxy hb.le
  have hz := mul_le_mul_of_nonneg_left hzy ha.le
  have hky := mul_pos hk hy
  nlinarith

theorem maximum_gap {a b k x y z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (k + a + b) * y = b * x + a * z) :
    k * y / (a + b) ≤ max (x - y) (z - y) := by
  apply (div_le_iff₀ (add_pos ha hb)).mpr
  have hx := mul_le_mul_of_nonneg_left (le_max_left (x-y) (z-y)) hb.le
  have hz := mul_le_mul_of_nonneg_left (le_max_right (x-y) (z-y)) ha.le
  nlinarith

end Rhone.Statistics.AsymmetricPairDesign
