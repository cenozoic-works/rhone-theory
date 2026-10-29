/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Cast
public import Rhone.Coalescent.Sfs

/-!
# Infinite-sites expectations: Watterson's estimator, the SFS, and Tajima's constants

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thms 1.20–1.22; tajima1989, p. 585,
eq. (1)–(9); fu1995, eq. (1), p. 174, eq. (22), p. 181. -/

@[expose] public section

namespace Rhone.Statistics

open Finset Coalescent Rhone.Combinatorics

def expSegSites (θ : ℚ) (n : ℕ) : ℚ := θ / 2 * expLength n

def varSegSites (θ : ℚ) (n : ℕ) : ℚ := θ / 2 * expLength n + (θ / 2) ^ 2 * varLength n

def tajimaA1 (n : ℕ) : ℚ := harmonic (n - 1)

def tajimaA2 (n : ℕ) : ℚ := ∑ i ∈ Icc 1 (n - 1), (1 : ℚ) / (i : ℚ) ^ 2

def tajimaB1 (n : ℕ) : ℚ := ((n : ℚ) + 1) / (3 * ((n : ℚ) - 1))

def tajimaB2 (n : ℕ) : ℚ := 2 * ((n : ℚ) ^ 2 + n + 3) / (9 * n * ((n : ℚ) - 1))

def tajimaC1 (n : ℕ) : ℚ := tajimaB1 n - 1 / tajimaA1 n

def tajimaC2 (n : ℕ) : ℚ :=
  tajimaB2 n - ((n : ℚ) + 2) / (tajimaA1 n * n) + tajimaA2 n / tajimaA1 n ^ 2

def tajimaE1 (n : ℕ) : ℚ := tajimaC1 n / tajimaA1 n

def tajimaE2 (n : ℕ) : ℚ := tajimaC2 n / (tajimaA1 n ^ 2 + tajimaA2 n)

def wattersonEstimator (n : ℕ) (S : ℚ) : ℚ := S / tajimaA1 n

def expPairwise (θ : ℚ) : ℚ := expSegSites θ 2

def expSfs (θ : ℚ) (n i : ℕ) : ℚ := θ / 2 * expSfsCoeff n i

theorem expSegSites_eq (θ : ℚ) (n : ℕ) : expSegSites θ n = θ * harmonic (n - 1) := by
  unfold expSegSites
  rw [expLength_eq]
  ring

theorem wattersonEstimator_unbiased (θ : ℚ) {n : ℕ} (hn : 2 ≤ n) :
    wattersonEstimator n (expSegSites θ n) = θ := by
  have h : harmonic (n - 1) ≠ 0 := by
    have : 0 < harmonic (n - 1) := zero_lt_harmonic (by omega)
    exact this.ne'
  unfold wattersonEstimator tajimaA1
  rw [expSegSites_eq]
  field_simp

theorem expPairwise_eq (θ : ℚ) : expPairwise θ = θ := by
  unfold expPairwise
  rw [expSegSites_eq]
  simp

theorem expSfs_eq (θ : ℚ) {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    expSfs θ n i = θ / i := by
  unfold expSfs
  rw [expSfsCoeff_eq hi hin]
  have : (i : ℚ) ≠ 0 := by positivity
  field_simp

theorem sum_expSfs (θ : ℚ) (n : ℕ) :
    ∑ i ∈ Icc 1 (n - 1), expSfs θ n i = expSegSites θ n := by
  rw [expSegSites_eq, harmonic_eq_sum_Icc_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h1, h2⟩ := mem_Icc.1 hi
  rw [expSfs_eq θ h1 (by omega)]
  ring

theorem expPairwise_of_sfs (θ : ℚ) {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Icc 1 (n - 1), (i * (n - i) : ℚ) / (n.choose 2 : ℚ) * expSfs θ n i = θ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hC : ((m + 2).choose 2 : ℚ) = (m + 2) * (m + 1) / 2 := by
    rw [Nat.cast_choose_two ℚ]; push_cast; ring
  have hCne : ((m + 2).choose 2 : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ m + 2)).ne'
  have hterm : ∀ i ∈ Icc 1 (m + 2 - 1),
      ((i : ℚ) * (((m + 2 : ℕ) : ℚ) - i)) / ((m + 2).choose 2 : ℚ) * expSfs θ (m + 2) i =
        θ / ((m + 2).choose 2 : ℚ) * (((m + 2 : ℕ) : ℚ) - i) := by
    intro i hi
    have hi1 := (mem_Icc.1 hi).1
    have hi2 := (mem_Icc.1 hi).2
    rw [expSfs_eq θ hi1 (by omega)]
    have : (i : ℚ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, show m + 2 - 1 = m + 1 by omega,
    Rhone.Combinatorics.sum_Icc_sub]
  push_cast at hC ⊢
  rw [hC]
  have : (m : ℚ) + 2 ≠ 0 := by positivity
  have : (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem tajima_numerator_expectation (θ : ℚ) {n : ℕ} (hn : 2 ≤ n) :
    expPairwise θ - wattersonEstimator n (expSegSites θ n) = 0 := by
  rw [expPairwise_eq, wattersonEstimator_unbiased θ hn, sub_self]

theorem varSegSites_eq (θ : ℚ) (n : ℕ) :
    varSegSites θ n = θ * tajimaA1 n + θ ^ 2 * tajimaA2 n := by
  unfold varSegSites tajimaA1 tajimaA2
  rw [expLength_eq, varLength_eq]
  ring

end Rhone.Statistics
