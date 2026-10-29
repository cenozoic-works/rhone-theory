/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-! # Hoeffding concentration for independent [0,1]-valued observations -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem subGaussian_unit_interval_sum {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ) {N : ℕ}
    (h_bound : ∀ i < N, ∀ᵐ ω ∂μ, X i ω ∈ Icc (0 : ℝ) 1) :
    HasSubgaussianMGF
      (fun ω => ∑ i ∈ Finset.range N, (X i ω - ∫ v, X i v ∂μ))
      ((N : ℝ≥0) * (1/4)) μ := by
  have h_center : iIndepFun (fun i ω => X i ω - ∫ v, X i v ∂μ) μ := by
    simpa only [Function.comp_def] using h_indep.comp
      (fun i x => x - ∫ v, X i v ∂μ) (fun _ => measurable_id.sub_const _)
  have h_sub : ∀ i ∈ Finset.range N,
      HasSubgaussianMGF (fun ω => X i ω - ∫ v, X i v ∂μ) (1/4 : ℝ≥0) μ := by
    intro i hi
    convert! hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bound i (Finset.mem_range.mp hi)) using 1
    norm_num
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    HasSubgaussianMGF.sum_of_iIndepFun h_center h_sub

omit [IsProbabilityMeasure μ] in
theorem measure_abs_ge_of_subGaussian {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε^2 / (2*c)) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    rw [le_abs]
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω})
        ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε^2 / (2*c)) + Real.exp (-ε^2 / (2*c)) :=
      add_le_add (h.measure_ge_le hε) (h.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε^2 / (2*c)) := by ring

theorem measure_centered_sum_abs_ge {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i < N, ∀ᵐ ω ∂μ, X i ω ∈ Icc (0 : ℝ) 1)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | (N : ℝ)*η ≤ |∑ i ∈ Finset.range N, (X i ω - ∫ v, X i v ∂μ)|}
      ≤ 2 * Real.exp (-2*(N : ℝ)*η^2) := by
  have hs := measure_abs_ge_of_subGaussian
    (subGaussian_unit_interval_sum h_indep h_meas h_bound) (mul_nonneg (Nat.cast_nonneg N) hη)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert! hs using 1
  congr 2
  push_cast
  field_simp [hNr]
  ring

theorem measure_centered_sum_abs_ge_ennreal {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i < N, ∀ᵐ ω ∂μ, X i ω ∈ Icc (0 : ℝ) 1)
    {η : ℝ} (hη : 0 ≤ η) :
    μ {ω | (N : ℝ)*η ≤ |∑ i ∈ Finset.range N, (X i ω - ∫ v, X i v ∂μ)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2*(N : ℝ)*η^2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measure_centered_sum_abs_ge h_indep h_meas hN h_bound hη)

end Rhone.Statistics.Identifiability

namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measure_sample_mean_abs_ge {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ j, AEMeasurable (X j) μ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ j < N, ∀ᵐ ω ∂μ, X j ω ∈ Icc (0 : ℝ) 1) {p : ℝ}
    (h_mean : ∀ j < N, (∫ v, X j v ∂μ) = p) {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | η ≤ |(∑ j ∈ Finset.range N, X j ω) / (N : ℝ) - p|}
      ≤ 2 * Real.exp (-2*(N : ℝ)*η^2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum (ω : Ω) :
      (∑ j ∈ Finset.range N, (X j ω - ∫ v, X j v ∂μ)) =
        (∑ j ∈ Finset.range N, X j ω) - (N : ℝ)*p := by
    rw [Finset.sum_sub_distrib]
    congr 1
    calc
      (∑ j ∈ Finset.range N, ∫ v, X j v ∂μ) = ∑ _j ∈ Finset.range N, p :=
        Finset.sum_congr rfl fun j hj => h_mean j (Finset.mem_range.mp hj)
      _ = (N : ℝ)*p := by simp
  have hset : {ω | η ≤ |(∑ j ∈ Finset.range N, X j ω) / (N : ℝ) - p|} =
      {ω | (N : ℝ)*η ≤ |∑ j ∈ Finset.range N, (X j ω - ∫ v, X j v ∂μ)|} := by
    ext ω
    simp only [mem_ofPred_eq, hsum]
    have heq : (∑ j ∈ Finset.range N, X j ω) / (N : ℝ) - p =
        ((∑ j ∈ Finset.range N, X j ω) - (N : ℝ)*p) / (N : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hNr, le_div_iff₀ hNr]
    simp only [mul_comm]
  rw [hset]
  exact measure_centered_sum_abs_ge h_indep h_meas hN h_bound hη

theorem measure_four_frequency_abs_ge {X : Fin 4 → ℕ → Ω → ℝ}
    (h_indep : ∀ i, iIndepFun (X i) μ)
    (h_meas : ∀ i j, AEMeasurable (X i j) μ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i j, j < N → ∀ᵐ ω ∂μ, X i j ω ∈ Icc (0 : ℝ) 1) {p : Fin 4 → ℝ}
    (h_mean : ∀ i j, j < N → (∫ v, X i j v ∂μ) = p i)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | ∃ i : Fin 4, η ≤ |(∑ j ∈ Finset.range N, X i j ω) / (N : ℝ) - p i|}
      ≤ 8 * Real.exp (-2*(N : ℝ)*η^2) := by
  have hset : {ω | ∃ i : Fin 4,
      η ≤ |(∑ j ∈ Finset.range N, X i j ω) / (N : ℝ) - p i|} =
      ⋃ i : Fin 4, {ω | η ≤ |(∑ j ∈ Finset.range N, X i j ω) / (N : ℝ) - p i|} := by
    ext ω
    simp
  rw [hset]
  calc
    _ ≤ ∑ i : Fin 4,
        μ.real {ω | η ≤ |(∑ j ∈ Finset.range N, X i j ω) / (N : ℝ) - p i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin 4, 2 * Real.exp (-2*(N : ℝ)*η^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact measure_sample_mean_abs_ge (h_indep i) (h_meas i) hN (h_bound i) (h_mean i) hη
    _ = 8 * Real.exp (-2*(N : ℝ)*η^2) := by simp; ring

theorem measure_four_frequency_abs_ge_ennreal {X : Fin 4 → ℕ → Ω → ℝ}
    (h_indep : ∀ i, iIndepFun (X i) μ)
    (h_meas : ∀ i j, AEMeasurable (X i j) μ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i j, j < N → ∀ᵐ ω ∂μ, X i j ω ∈ Icc (0 : ℝ) 1) {p : Fin 4 → ℝ}
    (h_mean : ∀ i j, j < N → (∫ v, X i j v ∂μ) = p i)
    {η : ℝ} (hη : 0 ≤ η) :
    μ {ω | ∃ i : Fin 4, η ≤ |(∑ j ∈ Finset.range N, X i j ω) / (N : ℝ) - p i|}
      ≤ ENNReal.ofReal (8 * Real.exp (-2*(N : ℝ)*η^2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measure_four_frequency_abs_ge h_indep h_meas hN h_bound h_mean hη)

end Rhone.Statistics.Identifiability
