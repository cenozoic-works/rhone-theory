/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.Price
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Hamilton's regression criterion from the Price equation

Source: price1972, pp. 486–488, eq. A11, A18; hamilton1964a, pp. 14–15. -/

@[expose] public section

namespace Rhone.Statistics

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Source: price1972, p. 485, eq. A1. -/
theorem kin_mean_const (a : ℝ) : popMean (fun _ : ι => a) = a := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

omit [Nonempty ι] in
/-- Source: price1972, p. 485, eq. A1. -/
theorem kin_mean_mul (a : ℝ) (f : ι → ℝ) :
    popMean (fun i => a * f i) = a * popMean f := by
  simp only [popMean, ← Finset.mul_sum, mul_div_assoc]

/-- Source: price1972, p. 488, eq. A18. -/
theorem kin_covariance (w z y e : ι → ℝ) (a b c : ℝ)
    (hfit : ∀ i, w i = a - c * z i + b * y i + e i) :
    popCov w z = -c * popCov z z + b * popCov y z + popCov e z := by
  have hw : w = fun i => a - c * z i + b * y i + e i := funext hfit
  rw [hw]
  simp only [popCov, add_mul, sub_mul, mul_assoc, popMean_add, popMean_sub,
    kin_mean_const, kin_mean_mul]
  ring

/-- Source: price1972, p. 488, eq. A18; hamilton1964a, pp. 14–15. -/
noncomputable def relatedness (y z : ι → ℝ) : ℝ := popCov y z / popCov z z

/-- Source: price1972, pp. 486–488, eq. A11, A18; hamilton1964a, pp. 14–15. -/
theorem hamilton_price (w z y e : ι → ℝ) (a b c : ℝ)
    (hw : 0 < popMean w) (hz : 0 < popCov z z)
    (hfit : ∀ i, w i = a - c * z i + b * y i + e i)
    (hres : popCov e z = 0) :
    nextMean w z - popMean z =
      popCov z z * (b * relatedness y z - c) / popMean w := by
  rw [robertson_price w z hw.ne', kin_covariance w z y e a b c hfit, hres,
    add_zero, relatedness]
  congr 1
  field_simp [hz.ne']
  ring

/-- Source: price1972, pp. 486–488, eq. A11, A18; hamilton1964a, pp. 14–15. -/
theorem hamilton_price_positive_iff (w z y e : ι → ℝ) (a b c : ℝ)
    (hw : 0 < popMean w) (hz : 0 < popCov z z)
    (hfit : ∀ i, w i = a - c * z i + b * y i + e i)
    (hres : popCov e z = 0) :
    0 < nextMean w z - popMean z ↔ c < b * relatedness y z := by
  rw [hamilton_price w z y e a b c hw hz hfit hres, div_pos_iff_of_pos_right hw,
    mul_pos_iff_of_pos_left hz, sub_pos]

end Rhone.Statistics
