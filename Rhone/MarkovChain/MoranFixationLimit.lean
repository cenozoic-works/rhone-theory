/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.FixationHarmonic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Moran fixation probability: scaling limit and weak-selection derivative

Source: moran1958; kimura1962, p. 715, eq. (8)–(9). -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset Filter Topology

private theorem tendsto_natCast_mul_log_one_add_div (σ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log (1 + σ / N)) atTop (𝓝 σ) :=
  (Real.tendsto_mul_log_one_add_div_atTop σ).comp tendsto_natCast_atTop_atTop

private theorem tendsto_inv_one_add_div_pow_floor (σ : ℝ) {x : ℝ} (hx0 : 0 ≤ x) :
    Tendsto (fun N : ℕ => ((1 + σ / N)⁻¹) ^ ⌊x * N⌋₊) atTop (𝓝 (Real.exp (-(σ * x)))) := by
  have hfloor : Tendsto (fun N : ℕ => ((⌊x * N⌋₊ : ℕ) : ℝ) / N) atTop (𝓝 x) :=
    (tendsto_nat_floor_mul_div_atTop hx0).comp tendsto_natCast_atTop_atTop
  have hprod := hfloor.mul (tendsto_natCast_mul_log_one_add_div σ)
  have hexp := (Real.continuous_exp.tendsto _).comp hprod.neg
  have hbase : Tendsto (fun N : ℕ => 1 + σ / (N : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat σ).const_add (1 : ℝ)
  have hlim : Real.exp (-(x * σ)) = Real.exp (-(σ * x)) := by rw [mul_comm]
  rw [← hlim]
  refine hexp.congr' ?_
  filter_upwards [hbase.eventually_const_lt zero_lt_one, eventually_gt_atTop 0] with N hpos hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have harg : -(((⌊x * N⌋₊ : ℕ) : ℝ) / N * ((N : ℝ) * Real.log (1 + σ / N))) =
      ((⌊x * N⌋₊ : ℕ) : ℝ) * Real.log ((1 + σ / N)⁻¹) := by
    rw [Real.log_inv]
    field_simp
  change Real.exp (-(((⌊x * N⌋₊ : ℕ) : ℝ) / N * ((N : ℝ) * Real.log (1 + σ / N)))) = _
  rw [harg, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hpos)]

/-- Source: moran1958; kimura1962, p. 715, eq. (8). -/
theorem tendsto_moranFixProb_kimura {σ x : ℝ} (hσ : σ ≠ 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => moranFixProb N (1 + σ / N) ⌊x * N⌋₊) atTop
      (𝓝 ((1 - Real.exp (-(σ * x))) / (1 - Real.exp (-σ)))) := by
  have _ := hx1
  have hnum := (tendsto_inv_one_add_div_pow_floor σ hx0).const_sub (1 : ℝ)
  have hden0 : Tendsto (fun N : ℕ => ((1 + σ / N)⁻¹) ^ ⌊(1 : ℝ) * N⌋₊) atTop
      (𝓝 (Real.exp (-(σ * 1)))) := tendsto_inv_one_add_div_pow_floor σ zero_le_one
  have hden : Tendsto (fun N : ℕ => 1 - ((1 + σ / (N : ℝ))⁻¹) ^ N) atTop
      (𝓝 (1 - Real.exp (-σ))) := by
    simpa only [one_mul, mul_one, Nat.floor_natCast] using hden0.const_sub (1 : ℝ)
  have hne : 1 - Real.exp (-σ) ≠ 0 := by
    intro h
    have h1 : Real.exp (-σ) = 1 := by linarith
    exact hσ (neg_eq_zero.mp (Real.exp_eq_one_iff _ |>.mp h1))
  refine (hnum.div hden hne).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hr1 : 1 + σ / (N : ℝ) ≠ 1 := by
    intro h
    have h0 : σ / (N : ℝ) = 0 := by linarith
    exact (div_ne_zero hσ hNr) h0
  exact (moranFixProb_of_ne_one hr1 N _).symm

/-- Source: moran1958; durrett2008, Thm 1.31. -/
theorem tendsto_moranFixProb_neutral {x : ℝ} (hx0 : 0 ≤ x) :
    Tendsto (fun N : ℕ => moranFixProb N 1 ⌊x * N⌋₊) atTop (𝓝 x) := by
  simp only [moranFixProb_one]
  exact (tendsto_nat_floor_mul_div_atTop hx0).comp tendsto_natCast_atTop_atTop

private theorem hasDerivAt_geomSum_inv_one (n : ℕ) :
    HasDerivAt (fun r : ℝ => ∑ k ∈ range n, (r⁻¹) ^ k) (-((n : ℝ) * ((n : ℝ) - 1) / 2)) 1 := by
  have hval : ∑ k ∈ range n, (-(k : ℝ)) = -((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    induction n with
    | zero => simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, zero_div, neg_zero]
    | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have hterm : ∀ k ∈ range n, HasDerivAt (fun r : ℝ => (r⁻¹) ^ k) (-(k : ℝ)) 1 := by
    intro k _
    have h := (hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0)).fun_pow k
    simpa only [inv_one, one_pow, mul_one, mul_neg] using h
  have hsum := HasDerivAt.fun_sum hterm
  rwa [hval] at hsum

/-- Source: moran1958. -/
theorem hasDerivAt_moranFixProb_one {N : ℕ} (hN : 0 < N) (i : ℕ) :
    HasDerivAt (fun r : ℝ => moranFixProb N r i)
      ((i : ℝ) * ((N : ℝ) - i) / (2 * (N : ℝ))) 1 := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hval : ∀ n : ℕ, ∑ k ∈ range n, ((1 : ℝ)⁻¹) ^ k = n := fun n => by
    simp only [inv_one, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hd : ∑ k ∈ range N, ((1 : ℝ)⁻¹) ^ k ≠ 0 := by rw [hval]; exact hNr
  have h := (hasDerivAt_geomSum_inv_one i).fun_div (hasDerivAt_geomSum_inv_one N) hd
  rw [hval, hval] at h
  unfold moranFixProb
  convert h using 1
  field_simp
  ring

end Rhone.MarkovChain
