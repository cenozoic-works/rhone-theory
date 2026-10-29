/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableInitialCoordinate

/-! # Positive lower bound for diagonal entries of integrable-rate transition matrices -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrableTransition_diagonal_lower_bound (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    Real.exp (∫ u in s..t, Q u i i) ≤ inhomogeneousTransition Q s t i i := by
  let v := fun u => inhomogeneousTransition Q s u i
  let H := fun u => -(∫ z in s..u, Q z i i)
  have hi := LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable (hQi i i) s t
  have hHac : AbsolutelyContinuousOnInterval H s t :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg
  have hd : ∀ᵐ u, u ∈ uIcc s t →
      HasDerivAt (fun z => v z i) (∑ j, v u j * Q u j i) u := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQi] with u hu _
    exact hu s i i
  have hHd : ∀ᵐ u, u ∈ uIcc s t → HasDerivAt H (-Q u i i) u := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (hQi i i)] with u hu _
    exact (hu s).neg
  have hbound : ∀ᵐ u, u ∈ uIcc s t →
      -(-Q u i i) * v u i ≤ ∑ j, v u j * Q u j i := by
    filter_upwards [hQ] with u hu hmem
    have hsu : s ≤ u := (by simpa only [uIcc_of_le hst, mem_Icc] using hmem : s ≤ u ∧ u ≤ t).1
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, v u j * Q u j i := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (integrableTransition_nonneg Q hQi hQ hs hsu i j)
        (hu (hs.trans hsu) j i (Finset.mem_erase.mp hj).1)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simpa only [neg_neg, mul_comm] using le_add_of_nonneg_left hrest
  have h := ac_comparison_lower (fun u => v u i) (fun u => ∑ j, v u j * Q u j i)
    H (fun u => -Q u i i) s t hst (integrableTransition_entry_ac_right Q hQi s s t i i)
    hHac hd hHd hbound
  simpa [v, H, integrableTransition_self Q hQi] using h

lemma integrableTransition_diagonal_positive (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    0 < inhomogeneousTransition Q s t i i :=
  (Real.exp_pos _).trans_le (integrableTransition_diagonal_lower_bound Q hQi hQ hs hst i)

end Rhone.Statistics.Identifiability
