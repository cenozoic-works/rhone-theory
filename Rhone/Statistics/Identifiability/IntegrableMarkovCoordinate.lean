/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovFlow

/-! # Coordinate survival under locally integrable Metzler evolution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

theorem integrable_row_coordinate_lower_bound
    (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ) (j : ι)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i k, i ≠ k → 0 ≤ Q t i k)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ k,
      HasDerivAt (fun s => v s k) (∑ i, v t i * Q t i k) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hdiag : LocallyIntegrable (fun s => Q s j j) volume)
    {t : ℝ} (ht : 0 ≤ t) :
    v 0 j * Real.exp (∫ s in (0 : ℝ)..t, Q s j j) ≤ v t j := by
  classical
  let H : ℝ → ℝ := fun s => -(∫ u in (0 : ℝ)..s, Q u j j)
  have hHac : AbsolutelyContinuousOnInterval H 0 t :=
    ((LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hdiag 0
      t).absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg
  have hd : ∀ᵐ s, s ∈ uIcc 0 t →
      HasDerivAt (fun u => v u j) (∑ i, v s i * Q s i j) s := by
    filter_upwards [he] with s hs hmem
    exact hs ((by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1) j
  have hHd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt H (-Q s j j) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hdiag] with s hs _
    exact (hs 0).neg
  have hbound : ∀ᵐ s, s ∈ uIcc 0 t →
      -(-Q s j j) * v s j ≤ ∑ i, v s i * Q s i j := by
    filter_upwards [hQ] with s hs hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase j, v s i * Q s i j := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hnonneg s hs0 i) (hs hs0 i j (Finset.mem_erase.mp hi).1)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simpa only [neg_neg, mul_comm] using le_add_of_nonneg_left hrest
  have h := ac_comparison_lower (fun s => v s j) (fun s => ∑ i, v s i * Q s i j)
    H (fun s => -Q s j j) 0 t ht (hv t ht j) hHac hd hHd hbound
  simpa only [H, intervalIntegral.integral_same, neg_zero, zero_sub, neg_neg] using h

theorem integrable_row_coordinate_pos
    (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ) (j : ι)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i k, i ≠ k → 0 ≤ Q t i k)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ k,
      HasDerivAt (fun s => v s k) (∑ i, v t i * Q t i k) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hdiag : LocallyIntegrable (fun s => Q s j j) volume)
    (hzero : 0 < v 0 j) {t : ℝ} (ht : 0 ≤ t) :
    0 < v t j :=
  (mul_pos hzero (Real.exp_pos _)).trans_le
    (integrable_row_coordinate_lower_bound Q v j hQ hv he hnonneg hdiag ht)

end Rhone.Statistics.Identifiability
