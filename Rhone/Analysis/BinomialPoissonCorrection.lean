/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # The binomial weights against the Poisson weights to first order -/

@[expose] public section

namespace Rhone.Analysis.BinomialPoissonCorrection

open Real Filter Topology Finset

noncomputable def binomWeight (N : ℕ) (p : ℝ) (z : ℕ) : ℝ :=
  (N.choose z : ℝ) * p ^ z * (1 - p) ^ (N - z)

noncomputable def poissonTerm (μ : ℝ) (z : ℕ) : ℝ :=
  exp (-μ) * μ ^ z / (z.factorial : ℝ)

section FirstOrder

variable {a b : ℕ → ℝ} {α β : ℝ}

private theorem tendsto_one_of_firstOrder
    (h : Tendsto (fun N : ℕ => (N : ℝ) * (a N - 1)) atTop (𝓝 α)) :
    Tendsto a atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * (a N - 1) * (1 / (N : ℝ))) atTop (𝓝 (α * 0)) :=
    h.mul (tendsto_const_div_atTop_nhds_zero_nat 1)
  rw [mul_zero] at h1
  have h2 : Tendsto (fun N : ℕ => a N - 1) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  have h3 := h2.add_const 1
  rw [zero_add] at h3
  refine h3.congr fun N => ?_
  ring

private theorem firstOrder_mul
    (ha : Tendsto (fun N : ℕ => (N : ℝ) * (a N - 1)) atTop (𝓝 α))
    (hb : Tendsto (fun N : ℕ => (N : ℝ) * (b N - 1)) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => (N : ℝ) * (a N * b N - 1)) atTop (𝓝 (α + β)) := by
  have h := (ha.mul (tendsto_one_of_firstOrder hb)).add hb
  rw [mul_one] at h
  refine h.congr fun N => ?_
  ring

private theorem firstOrder_pow
    (ha : Tendsto (fun N : ℕ => (N : ℝ) * (a N - 1)) atTop (𝓝 α)) (z : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (a N ^ z - 1)) atTop (𝓝 (z * α)) := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h := firstOrder_mul ih ha
    have e : ((z + 1 : ℕ) : ℝ) * α = z * α + α := by
      push_cast
      ring
    rw [e]
    refine h.congr fun N => ?_
    rw [pow_succ]

private theorem firstOrder_one_sub_div (c : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((1 - c / N) - 1)) atTop (𝓝 (-c)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp
  ring

private theorem firstOrder_prod_range (z : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (∏ j ∈ Finset.range z, (1 - (j : ℝ) / N) - 1)) atTop
      (𝓝 (-∑ j ∈ Finset.range z, (j : ℝ))) := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h := firstOrder_mul ih (firstOrder_one_sub_div (z : ℝ))
    rw [Finset.sum_range_succ, neg_add]
    refine h.congr fun N => ?_
    rw [Finset.prod_range_succ]

private theorem tendsto_one_sub_div (μ : ℝ) :
    Tendsto (fun N : ℕ => 1 - μ / (N : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat μ).const_sub 1
  rw [sub_zero] at h
  exact h

private theorem firstOrder_inv (μ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((1 - μ / N)⁻¹ - 1)) atTop (𝓝 μ) := by
  have h1 := tendsto_one_sub_div μ
  have h2 : Tendsto (fun N : ℕ => μ * (1 - μ / (N : ℝ))⁻¹) atTop (𝓝 (μ * 1⁻¹)) :=
    (h1.inv₀ one_ne_zero).const_mul μ
  rw [inv_one, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, h1.eventually_ne one_ne_zero] with N hN hne
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hne' : (N : ℝ) - μ ≠ 0 := by
    intro h0
    apply hne
    rw [sub_eq_zero] at h0
    rw [← h0, div_self hN', sub_self]
  have e : 1 - μ / (N : ℝ) = ((N : ℝ) - μ) / N := by
    field_simp
  rw [e, inv_div]
  field_simp
  ring

end FirstOrder

private theorem abs_log_remainder_le {μ : ℝ} {N : ℕ} (hN : 2 * |μ| + 1 ≤ (N : ℝ)) :
    |(N : ℝ) * (μ + N * log (1 - μ / N)) + μ ^ 2 / 2| ≤ 2 * |μ| ^ 3 / N := by
  have hNpos : 0 < (N : ℝ) := by linarith [abs_nonneg μ]
  set x : ℝ := μ / N with hx
  have hxabs : |x| = |μ| / N := by
    rw [hx, abs_div, abs_of_pos hNpos]
  have hxhalf : |x| ≤ 1 / 2 := by
    rw [hxabs, div_le_iff₀ hNpos]
    linarith
  have hx1 : |x| < 1 := by linarith
  have key := Real.abs_log_sub_add_sum_range_le hx1 2
  have hsum : ∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1) = x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at key
  have hid : (N : ℝ) * (μ + N * log (1 - x)) + μ ^ 2 / 2
      = (N : ℝ) ^ 2 * (x + x ^ 2 / 2 + log (1 - x)) := by
    have hμ : μ = x * N := ((eq_div_iff hNpos.ne').1 hx).symm
    rw [hμ]
    ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hb : |x| ^ (2 + 1) / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have h3 : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
    have h4 : |x| ^ (2 + 1) = |x| ^ 3 := by norm_num
    have h5 := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - |x| by linarith) h3
    rw [h4]
    linarith
  calc (N : ℝ) ^ 2 * |x + x ^ 2 / 2 + log (1 - x)|
      ≤ (N : ℝ) ^ 2 * (2 * |x| ^ 3) :=
        mul_le_mul_of_nonneg_left (key.trans hb) (sq_nonneg _)
    _ = 2 * |μ| ^ 3 / N := by
        rw [hxabs]
        field_simp

theorem tendsto_mul_one_sub_div_pow_sub_one (μ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (exp μ * (1 - μ / N) ^ N - 1)) atTop
      (𝓝 (-(μ ^ 2 / 2))) := by
  set d : ℕ → ℝ := fun N => μ + N * log (1 - μ / N) with hd
  have hA : Tendsto (fun N : ℕ => (N : ℝ) * d N + μ ^ 2 / 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * |μ| ^ 3))
    filter_upwards [eventually_ge_atTop (⌈2 * |μ|⌉₊ + 1)] with N hN
    have h1 : ((⌈2 * |μ|⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : 2 * |μ| ≤ (⌈2 * |μ|⌉₊ : ℝ) := Nat.le_ceil _
    push_cast at h1
    rw [Real.norm_eq_abs]
    exact abs_log_remainder_le (by linarith)
  have hNd : Tendsto (fun N : ℕ => (N : ℝ) * d N) atTop (𝓝 (-(μ ^ 2 / 2))) := by
    have h := hA.add_const (-(μ ^ 2 / 2))
    rw [zero_add] at h
    refine h.congr fun N => ?_
    ring
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have h := hNd.mul (tendsto_const_div_atTop_nhds_zero_nat 1)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  have hB : Tendsto (fun N : ℕ => (N : ℝ) * (exp (d N) - 1 - d N)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => |(N : ℝ) * d N| * |d N|) atTop (𝓝 0) := by
      have h := hNd.abs.mul hd0.abs
      rw [abs_zero, mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hbound
    have hsmall : ∀ᶠ N in atTop, |d N| < 1 :=
      hd0.abs.eventually (gt_mem_nhds (by simp))
    filter_upwards [hsmall] with N hN
    have h := Real.abs_exp_sub_one_sub_id_le hN.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
    rw [abs_mul_abs_self, ← sq]
    exact h
  have hC : Tendsto (fun N : ℕ => (N : ℝ) * (exp (d N) - 1)) atTop (𝓝 (-(μ ^ 2 / 2))) := by
    have h := hNd.add hB
    rw [add_zero] at h
    refine h.congr fun N => ?_
    ring
  refine hC.congr' ?_
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < 1 - μ / (N : ℝ) :=
    (tendsto_one_sub_div μ).eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos] with N hN
  have e : exp (d N) = exp μ * (1 - μ / N) ^ N := by
    rw [hd]
    simp only
    rw [exp_add, Real.exp_nat_mul, exp_log hN]
  rw [e]

private theorem sum_range_natCast (z : ℕ) :
    ∑ j ∈ Finset.range z, (j : ℝ) = z * (z - 1) / 2 := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem choose_eq_prod {N z : ℕ} (hz : z ≤ N) (hN : 0 < N) :
    (N.choose z : ℝ)
      = (∏ j ∈ Finset.range z, (1 - (j : ℝ) / N)) * (N : ℝ) ^ z / z.factorial := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h1 : (z.factorial : ℝ) * N.choose z = ∏ i ∈ Finset.range z, ((N : ℝ) - i) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [Nat.cast_sub (by omega)]
  have h2 : ∏ i ∈ Finset.range z, (1 - (i : ℝ) / N)
      = (∏ i ∈ Finset.range z, ((N : ℝ) - i)) / (N : ℝ) ^ z := by
    have hc : (N : ℝ) ^ z = ∏ _i ∈ Finset.range z, (N : ℝ) := by simp
    rw [hc, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
  have hz' : (z.factorial : ℝ) ≠ 0 := by exact_mod_cast z.factorial_ne_zero
  rw [h2, div_mul_cancel₀ _ (pow_ne_zero z hN'), ← h1]
  field_simp

theorem binomWeight_eq (μ : ℝ) {N z : ℕ} (hz : z ≤ N) (hN : 0 < N)
    (hne : 1 - μ / (N : ℝ) ≠ 0) :
    binomWeight N (μ / N) z
      = poissonTerm μ z * ((∏ j ∈ Finset.range z, (1 - (j : ℝ) / N)) * ((1 - μ / N)⁻¹) ^ z
          * (exp μ * (1 - μ / N) ^ N)) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hz' : (z.factorial : ℝ) ≠ 0 := by exact_mod_cast z.factorial_ne_zero
  have he : exp (-μ) * exp μ = 1 := by
    rw [← exp_add]
    simp
  unfold binomWeight poissonTerm
  rw [choose_eq_prod hz hN, pow_sub₀ _ hne hz, inv_pow, div_pow]
  generalize (1 - μ / (N : ℝ)) ^ N = E
  have hyz : (1 - μ / (N : ℝ)) ^ z ≠ 0 := pow_ne_zero z hne
  generalize (1 - μ / (N : ℝ)) ^ z = Y at hyz
  generalize ∏ j ∈ Finset.range z, (1 - (j : ℝ) / N) = P
  have hNz : (N : ℝ) ^ z ≠ 0 := pow_ne_zero z hN'
  field_simp
  linear_combination (-(P * μ ^ z * E)) * he

theorem tendsto_mul_binomWeight_sub_poisson (μ : ℝ) (z : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (binomWeight N (μ / N) z - poissonTerm μ z)) atTop
      (𝓝 (-(poissonTerm μ z * (((z : ℝ) - μ) ^ 2 - z) / 2))) := by
  have hall := (firstOrder_mul
    (firstOrder_mul (firstOrder_prod_range z) (firstOrder_pow (firstOrder_inv μ) z))
    (tendsto_mul_one_sub_div_pow_sub_one μ)).const_mul (poissonTerm μ z)
  have hlim : poissonTerm μ z * (-∑ j ∈ Finset.range z, (j : ℝ) + z * μ + -(μ ^ 2 / 2))
      = -(poissonTerm μ z * (((z : ℝ) - μ) ^ 2 - z) / 2) := by
    rw [sum_range_natCast]
    ring
  rw [hlim] at hall
  refine hall.congr' ?_
  filter_upwards [eventually_ge_atTop z, eventually_gt_atTop 0,
    (tendsto_one_sub_div μ).eventually_ne one_ne_zero] with N hz hN hne
  rw [binomWeight_eq μ hz hN hne]
  ring

end Rhone.Analysis.BinomialPoissonCorrection
