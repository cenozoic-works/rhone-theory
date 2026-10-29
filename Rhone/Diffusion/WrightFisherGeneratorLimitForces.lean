/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.WrightFisher
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Drift coefficient under binomial sampling after selection and mutation

Source: ewens2004, ch. 4, ch. 5; crow_kimura1970, ch. 8. -/

@[expose] public section

namespace Rhone.Diffusion

open Finset Filter Topology MarkovChain

theorem sum_binomRow_freq_sub {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) = q - x := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have e : ∀ j : ℕ, binomRow N q j * ((j : ℝ) / N - x) =
      binomRow N q j * j / N - x * binomRow N q j := fun j => by ring
  simp only [e, sum_sub_distrib, ← sum_div, ← mul_sum, sum_binomRow_mul, sum_binomRow]
  field_simp

theorem sum_binomRow_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) ^ 2 =
      q * (1 - q) / N + (q - x) ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have e : ∀ j : ℕ, binomRow N q j * ((j : ℝ) / N - x) ^ 2 =
      binomRow N q j * ((j : ℝ) * j) / (N : ℝ) ^ 2 - 2 * x * (binomRow N q j * j / N)
        + x ^ 2 * binomRow N q j := fun j => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum, sum_binomRow_mul_mul,
    sum_binomRow_mul, sum_binomRow]
  field_simp
  ring

theorem hapMutSel_drift_error_le {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {N : ℕ} (hN : 2 * σ ≤ N) (hN1 : 1 ≤ N) :
    |(N : ℝ) * (∑ j ∈ range (N + 1),
          binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
            * ((j : ℝ) / N - x))
        - (1 - x) * (ν - σ * x)| ≤ 2 * σ * (ν + σ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  rw [sum_binomRow_freq_sub hN1]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = σ / N := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs2 : s ≤ 1 / 2 := by
    rw [hs, div_le_iff₀ hNpos]
    linarith
  have hσs : σ = s * N := by rw [hs]; field_simp
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 - s * x := ⟨_, rfl⟩
  have hD2 : 1 / 2 ≤ D := by
    rw [hD]
    nlinarith [mul_le_mul hs2 hx.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hDpos : 0 < D := by linarith
  have hsx0 : 0 ≤ s * x := mul_nonneg hs0 hx.1
  have hsx : s * x ≤ s := by nlinarith [hx.2]
  rw [← hs, ← hD]
  have e : (N : ℝ) * (ν / N + (1 - ν / N) * (x * (1 - s) / D) - x) - (1 - x) * (ν - σ * x) =
      (1 - x) * (ν - σ * x) * (s * x) / D := by
    rw [hσs]
    field_simp
    rw [hD]
    ring
  rw [e, abs_div, abs_mul, abs_mul, abs_of_pos hDpos, abs_of_nonneg hsx0,
    abs_of_nonneg (sub_nonneg.2 hx.2)]
  have hA : |ν - σ * x| ≤ ν + σ := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hσ hx.1, mul_le_mul_of_nonneg_left hx.2 hσ]
  have h1x : 1 - x ≤ 1 := by linarith [hx.1]
  have h1x0 : 0 ≤ 1 - x := sub_nonneg.2 hx.2
  calc (1 - x) * |ν - σ * x| * (s * x) / D
      ≤ 1 * (ν + σ) * s / (1 / 2) := by gcongr
    _ = 2 * σ * (ν + σ) / N := by
        rw [hs]
        field_simp

theorem hapMutSel_drift_tendsto {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => (N : ℝ) * (∑ j ∈ range (N + 1),
        binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
          * ((j : ℝ) / N - x)))
      atTop (𝓝 ((1 - x) * (ν - σ * x))) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * σ * (ν + σ)))
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * σ)] with N hN1 hN
  exact hapMutSel_drift_error_le hσ hν hx hN hN1

end Rhone.Diffusion
