/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.HaploidSelection
public import Rhone.Dynamics.HardyWeinberg
public import Rhone.MarkovChain.DriftHeterozygosity
public import Mathlib.Tactic.FieldSimp

/-! # F-statistics and the Wahlund identity -/

@[expose] public section

namespace Rhone.Statistics.FStatistics

open Finset Rhone.Dynamics MarkovChain

/-- Source: wright1951, Table 1, p. 323. -/
noncomputable def hweHet (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- Source: wright1951, p. 328. -/
noncomputable def fRatio (Hobs Href : ℝ) : ℝ := 1 - Hobs / Href

/-- Source: wright1951, p. 328. -/
theorem f_statistics_decomposition (HI HS HT : ℝ)
    (hHS : HS ≠ 0) (hHT : HT ≠ 0) :
    1 - fRatio HI HT = (1 - fRatio HI HS) * (1 - fRatio HS HT) := by
  unfold fRatio
  field_simp
  ring

/-- Source: wright1951, p. 330, p. 344; felsenstein_teg2019, eq. (IV-7), pp. 175–176. -/
theorem wahlund_identity {ι : Type*} [Fintype ι]
    (w p : ι → ℝ) (hw : ∑ i, w i = 1) :
    hweHet (wMean w p) - wMean w (fun i => hweHet (p i)) = 2 * wVar w p := by
  have hsum : ∑ i, w i * (2 * p i * (1 - p i)) =
      2 * ∑ i, w i * p i - 2 * ∑ i, w i * (p i * p i) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [wVar_eq_mean_sq_sub w p hw]
  have hcentral : wMean w (fun i => (p i - wMean w p) ^ 2) =
      wMean w (fun i => p i * p i) - wMean w p * wMean w p := by
    simpa only [wVar, wCov] using (wVar_eq_mean_sq_sub w p hw).symm
  rw [hcentral]
  simp only [hweHet, wMean, hsum]
  ring

/-- Source: wright1951, p. 330, p. 344; felsenstein_teg2019, eq. (IV-7), pp. 175–176. -/
theorem wahlund_deficit_nonneg {ι : Type*} [Fintype ι]
    (w p : ι → ℝ) (hw : ∑ i, w i = 1)
    (hw0 : ∀ i, 0 ≤ w i) :
    0 ≤ hweHet (wMean w p) - wMean w (fun i => hweHet (p i)) := by
  rw [wahlund_identity w p hw, wVar_eq_mean_sq_sub w p hw]
  exact mul_nonneg (by norm_num) (sum_nonneg fun i _ =>
    mul_nonneg (hw0 i) (sq_nonneg _))

/-- Source: wright1951, p. 330, p. 344; felsenstein_teg2019, eq. (IV-7), pp. 175–176. -/
theorem wahlund_zero_iff {ι : Type*} [Fintype ι]
    (w p : ι → ℝ) (hw : ∑ i, w i = 1)
    (hw0 : ∀ i, 0 < w i) :
    hweHet (wMean w p) - wMean w (fun i => hweHet (p i)) = 0 ↔
      ∀ i, p i = wMean w p := by
  rw [wahlund_identity w p hw, wVar_eq_mean_sq_sub w p hw]
  constructor
  · intro h
    have hsum : ∑ i, w i * (p i - wMean w p) ^ 2 = 0 := by
      change 2 * (∑ i, w i * (p i - wMean w p) ^ 2) = 0 at h
      linarith
    have hzero := (sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ univ) => mul_nonneg (hw0 i).le (sq_nonneg _))).mp hsum
    intro i
    have hi : (p i - wMean w p) ^ 2 = 0 :=
      (mul_eq_zero.mp (hzero i (mem_univ i))).resolve_left (hw0 i).ne'
    nlinarith [sq_nonneg (p i - wMean w p)]
  · intro h
    simp only [wMean]
    have hs : ∑ i, w i * (p i - wMean w p) ^ 2 = 0 := by
      apply sum_eq_zero
      intro i _
      rw [h i, sub_self, zero_pow (by omega), mul_zero]
    exact mul_eq_zero_of_right 2 hs

/-- Source: wright1931, p. 111. -/
theorem het_eq_hweHet (N i : ℕ) :
    Rhone.MarkovChain.het N i = hweHet ((i : ℝ) / N) := rfl

end Rhone.Statistics.FStatistics
