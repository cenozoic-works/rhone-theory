/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

/-! # Finite weighted variance identities used by the silent-window covariance proof -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.Identifiability.SilentWindow
variable {ι : Type*} [Fintype ι]

def mean (μ v : ι → ℝ) : ℝ := ∑ i, μ i * v i

def variance (μ v : ι → ℝ) : ℝ := ∑ i, μ i * (v i - mean μ v)^2

lemma variance_identity (μ v : ι → ℝ) (hμ : ∑ i, μ i = 1) :
    variance μ v = (∑ i, μ i * (v i)^2) - (mean μ v)^2 := by
  have he (i : ι) : μ i * (v i - mean μ v)^2 =
      μ i * (v i)^2 - 2 * mean μ v * (μ i * v i) + (mean μ v)^2 * μ i := by ring
  simp_rw [variance, he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (∑ i, μ i * (v i)^2) - 2 * mean μ v * mean μ v + (mean μ v)^2 * (∑ i, μ i) = _
  rw [hμ]
  ring

lemma variance_nonneg (μ v : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) : 0 ≤ variance μ v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)

lemma variance_pos (μ v : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hne : ∃ i j, v i ≠ v j) : 0 < variance μ v := by
  classical
  have hex : ∃ i, v i ≠ mean μ v := by
    by_contra! h
    obtain ⟨i, j, hij⟩ := hne
    exact hij ((h i).trans (h j).symm)
  obtain ⟨i, hi⟩ := hex
  have hp : 0 < μ i * (v i - mean μ v)^2 :=
    mul_pos (hμ i) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))
  change 0 < ∑ j, μ j * (v j - mean μ v)^2
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (hμ j).le (sq_nonneg (v j - mean μ v))) (Finset.mem_univ i))

lemma cubic_gap_pos (μ : ι → ℝ) (hμ : ∑ i, μ i = 1) (hp : ∀ i, 0 < μ i)
    (hne : ∃ i j, μ i ≠ μ j) :
    0 < (∑ i, (μ i)^3) - (∑ i, (μ i)^2)^2 := by
  have h := variance_pos μ μ hp hne
  rw [variance_identity μ μ hμ] at h
  have h1 : (∑ i, μ i * (μ i)^2) = ∑ i, (μ i)^3 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : mean μ μ = ∑ i, (μ i)^2 := by
    unfold mean
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [h1, h2] at h

end Rhone.Statistics.Identifiability.SilentWindow
