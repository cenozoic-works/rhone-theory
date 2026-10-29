/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependenceBudget.Transfer
public import Mathlib.Tactic.FieldSimp

/-! # The common reporting channel: column means, baseline, and retained variance -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel

structure Channel (K : ℕ) (H : Type*) [Fintype H] where
  positive : 0 < K
  row : Fin K → H → ℝ
  nonneg : ∀ i y, 0 ≤ row i y
  normalized : ∀ i, ∑ y, row i y = 1

variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def columnMean (E : Channel K H) (y : H) : ℝ :=
  (∑ i, E.row i y) / K

noncomputable def baseline (E : Channel K H) : ℝ := ∑ y, (columnMean E y)^2

noncomputable def retainedVariance (E : Channel K H) : ℝ :=
  (∑ i, ∑ y, (E.row i y - columnMean E y)^2) / K

def Informative (E : Channel K H) : Prop := ∃ i j y, E.row i y ≠ E.row j y

theorem column_mean_nonneg (E : Channel K H) (y : H) : 0 ≤ columnMean E y := by
  exact div_nonneg (Finset.sum_nonneg (fun i _ => E.nonneg i y)) (Nat.cast_nonneg K)

theorem column_mean_total (E : Channel K H) : ∑ y, columnMean E y = 1 := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  simp only [columnMean, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [E.normalized, hK]

theorem retained_variance_nonneg (E : Channel K H) : 0 ≤ retainedVariance E := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (Nat.cast_nonneg K)

theorem retained_variance_zero_iff (E : Channel K H) :
    retainedVariance E = 0 ↔ ∀ i y, E.row i y = columnMean E y := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  unfold retainedVariance
  rw [div_eq_zero_iff]
  simp only [hK, or_false]
  constructor
  · intro h i y
    have hi : (∑ y, (E.row i y - columnMean E y)^2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp h i (Finset.mem_univ i)
    have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
      hi y (Finset.mem_univ y)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hy)
  · intro h
    simp [h]

theorem retained_variance_pos_iff (E : Channel K H) :
    0 < retainedVariance E ↔ Informative E := by
  constructor
  · intro hv
    by_contra hn
    have heq : ∀ i j y, E.row i y = E.row j y := by
      intro i j y
      by_contra h
      exact hn ⟨i, j, y, h⟩
    have hz : retainedVariance E = 0 := (retained_variance_zero_iff E).mpr (by
      intro i y
      have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
      simp [columnMean, fun j => heq j i y, hK])
    linarith
  · rintro ⟨i, j, y, hij⟩
    apply lt_of_le_of_ne (retained_variance_nonneg E)
    intro hz
    have h := (retained_variance_zero_iff E).mp hz.symm
    exact hij ((h i y).trans (h j y).symm)

end Rhone.Statistics.PairObservationChannel
