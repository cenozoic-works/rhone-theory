/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteCountSeparationTopology
public import Rhone.Statistics.Identifiability.FinitePanelConcentration

/-! # The target-centred finite-count iid test -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Rhone.Statistics.Identifiability
namespace FiniteCountSeparation
open FinitePanelSampling

def cellIndicator (k x : ℕ × ℕ) : ℝ := if x = k then 1 else 0

def cellScore (k x : ℕ × ℕ) : ℝ := 2 * cellIndicator k x - 1

lemma cellScore_abs_le_one (k x : ℕ × ℕ) : |cellScore k x| ≤ 1 := by
  by_cases h : x = k <;> norm_num [cellScore, cellIndicator, h]

lemma cellIndicator_integral (ν : Measure (ℕ × ℕ)) (k : ℕ × ℕ) :
    (∫ x, cellIndicator k x ∂ν) = ν.real {k} := by
  have heq : cellIndicator k = ({k} : Set (ℕ × ℕ)).indicator (fun _ => (1 : ℝ)) := by
    ext x
    simp [cellIndicator, Set.indicator_apply]
  rw [heq]
  simpa only [smul_eq_mul, mul_one] using
    (integral_indicator_const (μ := ν) (1 : ℝ) (measurableSet_singleton k))

lemma cellScore_integral (ν : Measure (ℕ × ℕ)) [IsProbabilityMeasure ν]
    (k : ℕ × ℕ) : (∫ x, cellScore k x ∂ν) = 2 * ν.real {k} - 1 := by
  have hi : Integrable (cellIndicator k) ν := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x = k <;> simp [cellIndicator, hx]
  simp only [cellScore]
  rw [integral_sub (hi.const_mul 2) (integrable_const 1), integral_const_mul,
    cellIndicator_integral, integral_const, probReal_univ, one_smul]

def frequency {S : ℕ} (k : ℕ × ℕ) (x : Fin S → ℕ × ℕ) : ℝ :=
  sampleMean (cellIndicator k) x

lemma sampleMean_cellScore {S : ℕ} (hS : 0 < S) (k : ℕ × ℕ)
    (x : Fin S → ℕ × ℕ) : sampleMean (cellScore k) x = 2 * frequency k x - 1 := by
  have hSr : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [sampleMean, cellScore, frequency, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

theorem iid_count_table_error (ν : Measure (ℕ × ℕ)) [IsProbabilityMeasure ν]
    (K : ℕ) {S : ℕ} (hS : 0 < S) {ε : ℝ} (hε : 0 ≤ ε) :
    (iidLaw ν S).real {x | ∃ i ≤ K, ∃ j ≤ K,
      ε / 2 ≤ |frequency (i, j) x - ν.real {(i, j)}|} ≤
      2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  let cell : Fin (K + 1) × Fin (K + 1) → ℕ × ℕ := fun k => (k.1.val, k.2.val)
  have h := iid_finite_scores_abs_ge ν (fun k => cellScore (cell k))
    (fun _ => measurable_of_countable _) (fun k x => cellScore_abs_le_one (cell k) x) hS hε
  have heq : {x : Fin S → ℕ × ℕ | ∃ i ≤ K, ∃ j ≤ K,
      ε / 2 ≤ |frequency (i, j) x - ν.real {(i, j)}|} =
      {x | ∃ k : Fin (K + 1) × Fin (K + 1),
        ε ≤ |sampleMean (cellScore (cell k)) x - ∫ y, cellScore (cell k) y ∂ν|} := by
    ext x
    simp only [mem_ofPred_eq, sampleMean_cellScore hS, cellScore_integral]
    have he (k : ℕ × ℕ) : |2 * frequency k x - 1 - (2 * ν.real {k} - 1)| =
        2 * |frequency k x - ν.real {k}| := by
      rw [show 2 * frequency k x - 1 - (2 * ν.real {k} - 1) =
        2 * (frequency k x - ν.real {k}) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [he]
    constructor
    · rintro ⟨i, hi, j, hj, hij⟩
      exact ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), by dsimp [cell]; linarith⟩
    · rintro ⟨k, hk⟩
      exact ⟨k.1.val, by omega, k.2.val, by omega, by dsimp [cell] at hk; linarith⟩
  rw [heq]
  convert h using 1
  simp [Fintype.card_prod, Fintype.card_fin, pow_two]

def acceptTarget (target : ℕ × ℕ → ℝ) (K S : ℕ) (ε : ℝ) : Set (Fin S → ℕ × ℕ) :=
  {x | ∀ i ≤ K, ∀ j ≤ K, |frequency (i, j) x - target (i, j)| < ε / 2}

theorem target_error (ν : Measure (ℕ × ℕ)) [IsProbabilityMeasure ν]
    (K : ℕ) {S : ℕ} (hS : 0 < S) {ε : ℝ} (hε : 0 ≤ ε) :
    (iidLaw ν S).real (acceptTarget (fun k => ν.real {k}) K S ε)ᶜ ≤
      2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  have heq : (acceptTarget (fun k => ν.real {k}) K S ε)ᶜ =
      {x | ∃ i ≤ K, ∃ j ≤ K, ε / 2 ≤ |frequency (i, j) x - ν.real {(i, j)}|} := by
    ext x
    simp [acceptTarget, not_lt]
  rw [heq]
  exact iid_count_table_error ν K hS hε

theorem competitor_error (ν : Measure (ℕ × ℕ)) [IsProbabilityMeasure ν]
    (target : ℕ × ℕ → ℝ) (K : ℕ) {S : ℕ} (hS : 0 < S)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∃ i ≤ K, ∃ j ≤ K, ε ≤ |ν.real {(i, j)} - target (i, j)|) :
    (iidLaw ν S).real (acceptTarget target K S ε) ≤
      2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  apply le_trans (measureReal_mono ?_) (iid_count_table_error ν K hS hε)
  rintro x hx
  obtain ⟨i, hi, j, hj, hsep⟩ := hsep
  refine ⟨i, hi, j, hj, ?_⟩
  have hclose := hx i hi j hj
  have htri := abs_sub_le (ν.real {(i, j)}) (frequency (i, j) x) (target (i, j))
  rw [abs_sub_comm (ν.real {(i, j)}) (frequency (i, j) x)] at htri
  linarith

end FiniteCountSeparation
end Rhone.Statistics.Identifiability
