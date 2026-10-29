/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableTwoParameterFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkovIntervals

/-! # Stochasticity of the locally integrable two-parameter flow -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Elementwise
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrableTransition_nonneg (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : ι) :
    0 ≤ inhomogeneousTransition Q s t i j := by
  apply integrable_row_solution_nonneg_endpoint Q
    (fun u => inhomogeneousTransition Q s u i) hst hQi ?_
    (integrableTransition_entry_ac_right Q hQi s s t i) ?_ ?_ j
  · filter_upwards [hQ] with u hu hmem
    have hsu : s ≤ u := (by simpa only [uIcc_of_le hst, mem_Icc] using hmem :
      s ≤ u ∧ u ≤ t).1
    exact hu (hs.trans hsu)
  · filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQi] with u hu _ j
    exact hu s i j
  · intro k
    simp only [integrableTransition_self Q hQi, Matrix.one_apply]
    split_ifs <;> norm_num

theorem integrableTransition_row_sum_le_one (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    (∑ j, inhomogeneousTransition Q s t i j) ≤ 1 := by
  have hm := integrable_finiteRowODE_mass_le_endpoint Q
    (fun u => inhomogeneousTransition Q s u i) hst
    (integrableTransition_entry_ac_right Q hQi s s t i) (by
      filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQi] with u hu _ j
      exact hu s i j) (fun u hu j =>
      integrableTransition_nonneg Q hQi hQ hs
        (by simpa only [uIcc_of_le hst, mem_Icc] using hu : s ≤ u ∧ u ≤ t).1 i j) (by
      filter_upwards [hrows] with u hu hmem
      exact hu (hs.trans
        (by simpa only [uIcc_of_le hst, mem_Icc] using hmem : s ≤ u ∧ u ≤ t).1))
  simpa only [integrableTransition_self Q hQi, Matrix.one_apply,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hm

theorem integrableTransition_row_sum_eq_one (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    (∑ j, inhomogeneousTransition Q s t i j) = 1 := by
  have hm := integrable_finiteRowODE_mass_eq_endpoint Q
    (fun u => inhomogeneousTransition Q s u i)
    (integrableTransition_entry_ac_right Q hQi s s t i) (by
      filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQi] with u hu _ j
      exact hu s i j) (by
      filter_upwards [hrows] with u hu hmem
      exact hu (hs.trans
        (by simpa only [uIcc_of_le hst, mem_Icc] using hmem : s ≤ u ∧ u ≤ t).1))
  simpa only [integrableTransition_self Q hQi, Matrix.one_apply,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hm

theorem exists_integrable_substochastic_transition (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) :
    ∃ U : ℝ → ℝ → Matrix ι ι ℝ,
      Continuous (fun p : ℝ × ℝ => U p.1 p.2) ∧
      (∀ s, U s s = 1) ∧
      (∀ s u t, U s t = U s u * U u t) ∧
      (∀ s a b, AbsolutelyContinuousOnInterval (U s) a b) ∧
      (∀ t a b, AbsolutelyContinuousOnInterval (fun s => U s t) a b) ∧
      (∀ᵐ t, ∀ s, HasDerivAt (U s) (U s t * Q t) t) ∧
      (∀ᵐ s, ∀ t, HasDerivAt (fun u => U u t) (-(Q s * U s t)) s) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i j, 0 ≤ U s t i j) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i, (∑ j, U s t i j) ≤ 1) := by
  exact ⟨inhomogeneousTransition Q, integrableTransition_continuous Q hQi,
    integrableTransition_self Q hQi, integrableTransition_cocycle Q hQi,
    integrableTransition_ac_right Q hQi, integrableTransition_ac_left Q hQi,
    integrableTransition_matrix_ae_hasDerivAt_right Q hQi,
    integrableTransition_matrix_ae_hasDerivAt_left Q hQi,
    fun _ _ hs hst => integrableTransition_nonneg Q hQi hQ hs hst,
    fun _ _ hs hst => integrableTransition_row_sum_le_one Q hQi hQ hrows hs hst⟩

theorem exists_integrable_stochastic_transition (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0) :
    ∃ U : ℝ → ℝ → Matrix ι ι ℝ,
      Continuous (fun p : ℝ × ℝ => U p.1 p.2) ∧
      (∀ s, U s s = 1) ∧
      (∀ s u t, U s t = U s u * U u t) ∧
      (∀ s a b, AbsolutelyContinuousOnInterval (U s) a b) ∧
      (∀ t a b, AbsolutelyContinuousOnInterval (fun s => U s t) a b) ∧
      (∀ᵐ t, ∀ s, HasDerivAt (U s) (U s t * Q t) t) ∧
      (∀ᵐ s, ∀ t, HasDerivAt (fun u => U u t) (-(Q s * U s t)) s) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i j, 0 ≤ U s t i j) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i, (∑ j, U s t i j) = 1) := by
  exact ⟨inhomogeneousTransition Q, integrableTransition_continuous Q hQi,
    integrableTransition_self Q hQi, integrableTransition_cocycle Q hQi,
    integrableTransition_ac_right Q hQi, integrableTransition_ac_left Q hQi,
    integrableTransition_matrix_ae_hasDerivAt_right Q hQi,
    integrableTransition_matrix_ae_hasDerivAt_left Q hQi,
    fun _ _ hs hst => integrableTransition_nonneg Q hQi hQ hs hst,
    fun _ _ hs hst => integrableTransition_row_sum_eq_one Q hQi hrows hs hst⟩

end Rhone.Statistics.Identifiability
