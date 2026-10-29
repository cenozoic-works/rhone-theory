/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.HaploidSelection
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Multilevel Price decomposition

Source: price1972, pp. 487–488, eq. (A 14)–(A 17); frank1995_price, p. 376, eq. (4). -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Dynamics Finset

variable {G : Type*} [Fintype G] {J : G → Type*} [∀ g, Fintype (J g)]

/-- Source: price1972, p. 487, eq. (A 14); frank1995_price, p. 376, eq. (4). -/
noncomputable def groupedMean (p : G → ℝ) (q z : ∀ g, J g → ℝ) : ℝ :=
  wMean p (fun g => wMean (q g) (z g))

/-- Source: price1972, p. 487, eq. (A 14); frank1995_price, p. 376, eq. (4). -/
noncomputable def groupedNextMean (p : G → ℝ) (q w z' : ∀ g, J g → ℝ) : ℝ :=
  groupedMean p q (fun g i => w g i * z' g i) / groupedMean p q w

/-- Source: frank1995_price, p. 376, eq. (4). -/
theorem grouped_probability_normalized (p : G → ℝ) (q : ∀ g, J g → ℝ)
    (hp0 : ∀ g, 0 ≤ p g) (hp1 : ∑ g, p g = 1)
    (hq0 : ∀ g i, 0 ≤ q g i) (hq1 : ∀ g, ∑ i, q g i = 1) :
    (∀ g i, 0 ≤ p g * q g i) ∧ (∑ g, ∑ i, p g * q g i) = 1 := by
  constructor
  · exact fun g i => mul_nonneg (hp0 g) (hq0 g i)
  · simp_rw [← mul_sum, hq1, mul_one]
    exact hp1

/-- Source: price1972, p. 488, eq. (A 16)–(A 17); frank1995_price, p. 376, eq. (4). -/
theorem grouped_covariance_decomposition (p : G → ℝ) (q w z : ∀ g, J g → ℝ) :
    groupedMean p q (fun g i => w g i * z g i) -
      groupedMean p q w * groupedMean p q z =
    wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
      wMean p (fun g => wCov (q g) (w g) (z g)) := by
  simp only [groupedMean, wCov, wMean, mul_sub, sum_sub_distrib]
  ring

/-- Source: price1972, pp. 487–488, eq. (A 15)–(A 17); frank1995_price, p. 376, eq. (4). -/
theorem multilevel_price_equation (p : G → ℝ) (q w z z' : ∀ g, J g → ℝ)
    (hw : groupedMean p q w ≠ 0) :
    groupedNextMean p q w z' - groupedMean p q z =
      (wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
        wMean p (fun g => wCov (q g) (w g) (z g)) +
        groupedMean p q (fun g i => w g i * (z' g i - z g i))) /
        groupedMean p q w := by
  rw [← grouped_covariance_decomposition]
  have htrans : groupedMean p q (fun g i => w g i * (z' g i - z g i)) =
      groupedMean p q (fun g i => w g i * z' g i) -
      groupedMean p q (fun g i => w g i * z g i) := by
    simp only [groupedMean, wMean, mul_sub, sum_sub_distrib]
  rw [htrans, groupedNextMean]
  field_simp
  ring

end Rhone.Statistics
