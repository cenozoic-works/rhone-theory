/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableProjectionDuhamel
public import Rhone.Statistics.Identifiability.IntegrableTransitionStochastic

/-! # Stability of integrable-rate transition matrices under flow perturbation -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Elementwise

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrableTransition_interpolation_ae_hasDerivAt
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (s t : ℝ) :
    ∀ᵐ u, ∀ i j,
      HasDerivAt
        (fun v => (inhomogeneousTransition A s v * inhomogeneousTransition B v t) i j)
        ((inhomogeneousTransition A s u * (A u - B u) *
          inhomogeneousTransition B u t) i j) u := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right A hA,
    integrableTransition_ae_hasDerivAt_left B hB] with u hAu hBu i j
  have h := finiteMatrixProduct_hasDerivAt_at
    (inhomogeneousTransition A s) (fun v => inhomogeneousTransition B v t)
    (inhomogeneousTransition A s u * A u)
    (-(B u * inhomogeneousTransition B u t)) u (hAu s) (hBu t) i j
  simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, ← sub_eq_add_neg,
    ← Matrix.sub_mul, ← Matrix.mul_sub] using h

theorem integrableTransition_sub_eq_integral_entry
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (s t : ℝ) (i j : ι) :
    inhomogeneousTransition A s t i j - inhomogeneousTransition B s t i j =
      ∫ u in s..t, (inhomogeneousTransition A s u * (A u - B u) *
        inhomogeneousTransition B u t) i j := by
  have hac := finiteMatrixProduct_entry_ac
    (inhomogeneousTransition A s) (fun v => inhomogeneousTransition B v t) s t
    (integrableTransition_entry_ac_right A hA s s t)
    (integrableTransition_entry_ac_left B hB t s t) i j
  have h := ac_integral_eq_sub_ae hac (by
    filter_upwards [integrableTransition_interpolation_ae_hasDerivAt A B hA hB s t]
      with u hu _ using hu i j)
  simpa only [integrableTransition_self A hA, integrableTransition_self B hB,
    Matrix.mul_one, Matrix.one_mul] using h.symm

omit [DecidableEq ι] in
theorem matrix_triple_entry_abs_le (P D R : Matrix ι ι ℝ)
    (hP : ∀ i j, |P i j| ≤ 1) (hR : ∀ i j, |R i j| ≤ 1) (i j : ι) :
    |(P * D * R) i j| ≤ ∑ q, ∑ p, |D p q| := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  calc
    |∑ q, ∑ p, P i p * D p q * R q j| ≤
        ∑ q, |∑ p, P i p * D p q * R q j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, ∑ p, |P i p * D p q * R q j| :=
      Finset.sum_le_sum fun q _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, ∑ p, |D p q| := by
      apply Finset.sum_le_sum; intro q _
      apply Finset.sum_le_sum; intro p _
      rw [abs_mul, abs_mul]
      calc
        |P i p| * |D p q| * |R q j| ≤ 1 * |D p q| * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hP i p) (abs_nonneg _))
            (hR q j) (abs_nonneg _) (by positivity)
        _ = |D p q| := by ring

theorem integrableTransition_abs_sub_le_integral_entry
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    {s t : ℝ} (hst : s ≤ t)
    (hAc : ∀ u ∈ Icc s t, ∀ i j, |inhomogeneousTransition A s u i j| ≤ 1)
    (hBc : ∀ u ∈ Icc s t, ∀ i j, |inhomogeneousTransition B u t i j| ≤ 1)
    (i j : ι) :
    |inhomogeneousTransition A s t i j - inhomogeneousTransition B s t i j| ≤
      ∫ u in s..t, ∑ q, ∑ p, |A u p q - B u p q| := by
  rw [integrableTransition_sub_eq_integral_entry A B hA hB]
  have hi : LocallyIntegrable (fun u => ∑ q, ∑ p, |A u p q - B u p q|) volume := by
    apply locallyIntegrable_finsetSum; intro q _
    apply locallyIntegrable_finsetSum; intro p _
    exact fun u => ((hA p q u).sub (hB p q u)).norm
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le hst
  · filter_upwards [] with u hu
    rw [Real.norm_eq_abs]
    convert matrix_triple_entry_abs_le _ _ _
      (hAc u ⟨hu.1.le, hu.2⟩) (hBc u ⟨hu.1.le, hu.2⟩) i j using 1
    rfl
  · exact LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hi s t

theorem integrableTransition_abs_entry_le_one
    (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : ι) :
    |inhomogeneousTransition Q s t i j| ≤ 1 := by
  have hn := integrableTransition_nonneg Q hQi hQ hs hst
  rw [abs_of_nonneg (hn i j)]
  exact (Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j)).trans
    (integrableTransition_row_sum_le_one Q hQi hQ hrows hs hst i)

theorem integrableTransition_abs_sub_le_integral_of_subgenerator
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hAn : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ A u i j)
    (hAr : ∀ᵐ u, 0 ≤ u → ∀ i, ∑ j, A u i j ≤ 0)
    (hBn : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ B u i j)
    (hBr : ∀ᵐ u, 0 ≤ u → ∀ i, ∑ j, B u i j ≤ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : ι) :
    |inhomogeneousTransition A s t i j - inhomogeneousTransition B s t i j| ≤
      ∫ u in s..t, ∑ q, ∑ p, |A u p q - B u p q| := by
  apply integrableTransition_abs_sub_le_integral_entry A B hA hB hst
  · exact fun u hu => integrableTransition_abs_entry_le_one A hA hAn hAr hs hu.1
  · exact fun u hu => integrableTransition_abs_entry_le_one B hB hBn hBr
      (hs.trans hu.1) hu.2

end Rhone.Statistics.Identifiability
