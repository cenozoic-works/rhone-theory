/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentWindowVariance

/-! # Trace monotonicity for symmetric positive-semidefinite covariance kernels -/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma real_psd_symmetric {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) : A j i = A i j := by
  have h := congrFun (congrFun hA.isHermitian.eq i) j
  simpa only [conjTranspose_apply, star_trivial] using h

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have h := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simp only [dotProduct, Matrix.mulVec, star_one, Pi.star_apply, mul_one, one_mul,
    Matrix.hadamard_apply] at h
  change 0 ≤ ∑ i, ∑ j, A i j * B j i
  simpa only [real_psd_symmetric hB] using h

lemma trace_mul_lower_bound {A B D E : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (hE : E.PosSemidef)
    (hAD : (A - D).PosSemidef) (hBE : (B - E).PosSemidef) :
    (D * E).trace ≤ (A * B).trace := by
  have h1 := trace_mul_nonneg hD hBE
  have h2 := trace_mul_nonneg hAD hE
  have h3 := trace_mul_nonneg hAD hBE
  have he : (A * B).trace = (D * E).trace + (D * (B - E)).trace +
      ((A - D) * E).trace + ((A - D) * (B - E)).trace := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.trace_sub]
    ring
  linarith

end Rhone.Statistics.Identifiability.SilentWindow
