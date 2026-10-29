/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Cemetery
public import Rhone.Statistics.Identifiability.DensityPositive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Exact finite-horizon mass balance for a killed finite-state semigroup -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open MeasureTheory Set
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false in
theorem flowOutput_hasDerivAt_right {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (flowOutput Q i v 0) (flowOutput Q i (Q *ᵥ v) 0 t) t := by
  have h := (rowFunctional i v).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const Q t)
  convert! h using 1
  · funext x
    simp [flowOutput]
  · simp [flowOutput, ← Matrix.mulVec_mulVec]

noncomputable def exitRate {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  -(Q *ᵥ (fun _ => 1))

theorem exitRate_nonneg {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d) : 0 ≤ exitRate Q i := by
  simpa [exitRate, Matrix.mulVec, dotProduct] using neg_nonneg.mpr (hrow i)

theorem survival_hasDerivAt_exit {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (t : ℝ) :
    HasDerivAt (flowOutput Q i (fun _ => 1) 0)
      (-flowOutput Q i (exitRate Q) 0 t) t := by
  convert flowOutput_hasDerivAt_right Q i (fun _ => 1) t using 1
  simp [flowOutput, exitRate, Matrix.mulVec_neg]

theorem firstExit_mass_balance {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (T : ℝ) :
    (∫ t in 0..T, flowOutput Q i (exitRate Q) 0 t) =
      1 - flowOutput Q i (fun _ => 1) 0 T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => survival_hasDerivAt_exit Q i t)
    ((flowOutput_continuous Q i (exitRate Q) 0).neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg, flowOutput_initial] at h
  linarith

theorem survival_nonneg {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ flowOutput Q i (fun _ => 1) 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg Q hQ ht) (fun _ => zero_le_one) i

theorem firstExit_mass_le_one {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in 0..T, flowOutput Q i (exitRate Q) 0 t) ≤ 1 := by
  rw [firstExit_mass_balance]
  exact sub_le_self _ (survival_nonneg Q hQ i hT)

end Rhone.Statistics.Identifiability
