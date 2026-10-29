/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DriftHeterozygosity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Moments of the temporal change in allele frequency -/

@[expose] public section

namespace Rhone.Statistics.TemporalNe

open Finset MarkovChain

theorem expect_affine {N : ℕ} (P : CountKernel N) (hP : ∀ i, ∑ j, P i j = 1)
    (a b c : ℝ) (f g : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    P.expect (fun j => a * f j + b * g j + c) i =
      a * P.expect f i + b * P.expect g i + c := by
  have h : ∀ j, P i j * (a * f j + b * g j + c) =
      a * (P i j * f j) + b * (P i j * g j) + c * P i j := fun j => by ring
  simp only [CountKernel.expect, h, sum_add_distrib, ← mul_sum, hP i]
  ring

theorem expectIter_affine {N : ℕ} (P : CountKernel N) (hP : ∀ i, ∑ j, P i j = 1)
    (a b c : ℝ) (f g : Fin (N + 1) → ℝ) (t : ℕ) (i : Fin (N + 1)) :
    P.expectIter t (fun j => a * f j + b * g j + c) i =
      a * P.expectIter t f i + b * P.expectIter t g i + c := by
  induction t generalizing i with
  | zero => simp [CountKernel.expectIter]
  | succ t ih =>
    have h : P.expectIter t (fun j => a * f j + b * g j + c) =
        fun j => a * P.expectIter t f j + b * P.expectIter t g j + c := funext ih
    simp only [CountKernel.expectIter, h, expect_affine P hP]

private theorem wf_rows (N : ℕ) (i : Fin (N + 1)) : ∑ j, wf N i j = 1 :=
  (wf_isStochastic N).2 i

theorem wf_expectIter_count (N t : ℕ) (i : Fin (N + 1)) :
    (wf N).expectIter t (fun j => (j : ℝ)) i = i := by
  simpa using CountKernel.expectIter_eigen (wf N) 1 _ (by simpa using wf_expect_id N) t i

theorem sq_change_eq (N : ℕ) (p0 : ℝ) (j : ℕ) :
    ((j : ℝ) / N - p0) ^ 2 =
      (-1 / 2) * het N j + ((1 - 2 * p0) / N) * (j : ℝ) + p0 ^ 2 := by
  unfold het
  ring

theorem wf_drift_second_moment (N t : ℕ) (i : Fin (N + 1)) :
    (wf N).expectIter t (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      ((i : ℝ) / N) * (1 - (i : ℝ) / N) * (1 - (1 - 1 / (N : ℝ)) ^ t) := by
  have h : (fun j : Fin (N + 1) => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) =
      fun j : Fin (N + 1) => (-1 / 2) * het N j + ((1 - 2 * ((i : ℝ) / N)) / N) * (j : ℝ)
        + ((i : ℝ) / N) ^ 2 := funext fun j => sq_change_eq N _ (j : ℕ)
  rw [h, expectIter_affine (wf N) (wf_rows N), wf_expectIter_het, wf_expectIter_count]
  unfold het
  ring

theorem wf_standardized_drift_variance (N t : ℕ) (i : Fin (N + 1))
    (h0 : 0 < (i : ℕ)) (hN : (i : ℕ) < N) :
    (wf N).expectIter t (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i /
        (((i : ℝ) / N) * (1 - (i : ℝ) / N)) = 1 - (1 - 1 / (N : ℝ)) ^ t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hN)
  have hi : (0 : ℝ) < i := by exact_mod_cast h0
  have hiN : (i : ℝ) < N := by exact_mod_cast hN
  have hp : ((i : ℝ) / N) * (1 - (i : ℝ) / N) ≠ 0 := by
    have h1 : 0 < (i : ℝ) / N := div_pos hi hNpos
    have h2 : (i : ℝ) / N < 1 := (div_lt_one hNpos).2 hiN
    have : 0 < 1 - (i : ℝ) / N := by linarith
    positivity
  rw [wf_drift_second_moment, mul_div_cancel_left₀ _ hp]

noncomputable def driftNe (t : ℕ) (F : ℝ) : ℝ := 1 / (1 - (1 - F) ^ ((t : ℝ)⁻¹))

theorem driftNe_standardized {N : ℕ} (t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    driftNe t (1 - (1 - 1 / (N : ℝ)) ^ t) = N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ 1 - 1 / (N : ℝ) := by
    have : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hNr
    linarith
  have hroot : ((1 - 1 / (N : ℝ)) ^ t) ^ ((t : ℝ)⁻¹) = 1 - 1 / (N : ℝ) :=
    Real.pow_rpow_inv_natCast hc ht.ne'
  unfold driftNe
  rw [sub_sub_cancel, hroot]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem binom_sq_deviation (S : ℕ) (hS : 0 < S) (p q : ℝ) :
    ∑ x ∈ range (S + 1), binomRow S p x * (((x : ℝ) / S - q) ^ 2) =
      p * (1 - p) / S + (p - q) ^ 2 := by
  have hS0 : (S : ℝ) ≠ 0 := by positivity
  have h : ∀ x : ℕ, binomRow S p x * (((x : ℝ) / S - q) ^ 2) =
      (1 / (S : ℝ) ^ 2) * (binomRow S p x * ((x : ℝ) * x))
        + (-2 * q / S) * (binomRow S p x * x) + q ^ 2 * binomRow S p x := fun x => by
    field_simp
    ring
  simp only [h, sum_add_distrib, ← mul_sum, sum_binomRow_mul_mul, sum_binomRow_mul,
    sum_binomRow]
  field_simp
  ring

theorem binom_mean_frequency (S : ℕ) (hS : 0 < S) (p : ℝ) :
    ∑ x ∈ range (S + 1), binomRow S p x * ((x : ℝ) / S) = p := by
  have hS0 : (S : ℝ) ≠ 0 := by positivity
  have h : ∀ x : ℕ, binomRow S p x * ((x : ℝ) / S) = (1 / (S : ℝ)) * (binomRow S p x * x) :=
    fun x => by ring
  simp only [h, ← mul_sum, sum_binomRow_mul]
  field_simp

noncomputable def sampledExpect (N t S0 St : ℕ) (i : Fin (N + 1)) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ x0 ∈ range (S0 + 1), binomRow S0 ((i : ℝ) / N) x0 *
    (wf N).expectIter t
      (fun j => ∑ xt ∈ range (St + 1), binomRow St ((j : ℝ) / N) xt * F x0 xt) i

theorem wf_expected_frequency_het (N t : ℕ) (i : Fin (N + 1)) :
    (wf N).expectIter t (fun j => ((j : ℝ) / N) * (1 - (j : ℝ) / N)) i =
      (1 - 1 / (N : ℝ)) ^ t * (((i : ℝ) / N) * (1 - (i : ℝ) / N)) := by
  have h : (fun j : Fin (N + 1) => ((j : ℝ) / N) * (1 - (j : ℝ) / N)) =
      fun j : Fin (N + 1) => (1 / 2) * het N j + 0 * (j : ℝ) + 0 :=
    funext fun j => by unfold het; ring
  rw [h, expectIter_affine (wf N) (wf_rows N), wf_expectIter_het]
  unfold het
  ring

theorem temporal_sampled_msd_decomposition (N t S0 St : ℕ) (i : Fin (N + 1))
    (hS0 : 0 < S0) (hSt : 0 < St) :
    sampledExpect N t S0 St i (fun x0 xt => ((xt : ℝ) / St - (x0 : ℝ) / S0) ^ 2) =
      (wf N).expectIter t (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i
        + ((i : ℝ) / N) * (1 - (i : ℝ) / N) / S0
        + (wf N).expectIter t (fun j => ((j : ℝ) / N) * (1 - (j : ℝ) / N)) i / St := by
  have hSt0 : (St : ℝ) ≠ 0 := by positivity
  have hS00 : (S0 : ℝ) ≠ 0 := by positivity
  rw [wf_drift_second_moment, wf_expected_frequency_het]
  unfold sampledExpect
  have inner : ∀ x0 : ℕ,
      (wf N).expectIter t (fun j => ∑ xt ∈ range (St + 1), binomRow St ((j : ℝ) / N) xt *
        (((xt : ℝ) / St - (x0 : ℝ) / S0) ^ 2)) i =
      ((1 / 2) * (1 / (St : ℝ)) - 1 / 2) * ((1 - 1 / (N : ℝ)) ^ t * het N i)
        + ((1 - 2 * ((x0 : ℝ) / S0)) * ((i : ℝ) / N)) + ((x0 : ℝ) / S0) ^ 2 := by
    intro x0
    have h : (fun j : Fin (N + 1) => ∑ xt ∈ range (St + 1), binomRow St ((j : ℝ) / N) xt *
        (((xt : ℝ) / St - (x0 : ℝ) / S0) ^ 2)) =
        fun j : Fin (N + 1) => (((1 / 2) * (1 / (St : ℝ)) - 1 / 2) * het N j)
          + ((1 - 2 * ((x0 : ℝ) / S0)) / N) * (j : ℝ) + ((x0 : ℝ) / S0) ^ 2 := by
      funext j
      rw [binom_sq_deviation St hSt]
      unfold het
      ring
    rw [h]
    have := expectIter_affine (wf N) (wf_rows N) (((1 / 2) * (1 / (St : ℝ)) - 1 / 2))
      ((1 - 2 * ((x0 : ℝ) / S0)) / N) (((x0 : ℝ) / S0) ^ 2) (fun j => het N j)
      (fun j => (j : ℝ)) t i
    rw [this, wf_expectIter_het, wf_expectIter_count]
    ring
  simp only [inner]
  set p := (i : ℝ) / N with hp
  have hrow : ∑ x0 ∈ range (S0 + 1), binomRow S0 p x0 = 1 := sum_binomRow S0 p
  have hmean := binom_mean_frequency S0 hS0 p
  have hsq := binom_sq_deviation S0 hS0 p 0
  simp only [sub_zero] at hsq
  have hexp : ∀ x0 : ℕ, binomRow S0 p x0 *
      (((1 / 2) * (1 / (St : ℝ)) - 1 / 2) * ((1 - 1 / (N : ℝ)) ^ t * het N i)
        + ((1 - 2 * ((x0 : ℝ) / S0)) * p) + ((x0 : ℝ) / S0) ^ 2) =
      (((1 / 2) * (1 / (St : ℝ)) - 1 / 2) * ((1 - 1 / (N : ℝ)) ^ t * het N i) + p) *
          binomRow S0 p x0
        + (-2 * p) * (binomRow S0 p x0 * ((x0 : ℝ) / S0))
        + binomRow S0 p x0 * (((x0 : ℝ) / S0) ^ 2) := fun x0 => by ring
  simp only [hexp, sum_add_distrib, ← mul_sum, hrow, hmean]
  rw [hsq]
  have hh : het N i = 2 * p * (1 - p) := by simp [het, hp]
  rw [hh]
  field_simp
  ring

theorem temporal_sampled_msd_closed (N t S0 St : ℕ) (i : Fin (N + 1))
    (hS0 : 0 < S0) (hSt : 0 < St) :
    sampledExpect N t S0 St i (fun x0 xt => ((xt : ℝ) / St - (x0 : ℝ) / S0) ^ 2) =
      ((i : ℝ) / N) * (1 - (i : ℝ) / N) *
        ((1 - (1 - 1 / (N : ℝ)) ^ t) + 1 / S0 + (1 - 1 / (N : ℝ)) ^ t / St) := by
  rw [temporal_sampled_msd_decomposition N t S0 St i hS0 hSt, wf_drift_second_moment,
    wf_expected_frequency_het]
  ring

end Rhone.Statistics.TemporalNe
