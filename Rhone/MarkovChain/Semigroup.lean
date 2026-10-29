/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateChain
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue

/-! # The transition semigroup of a finite continuous-time chain -/

@[expose] public section

namespace Rhone.MarkovChain.RateChain

open Finset NormedSpace

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

noncomputable def semigroup (t : ℝ) : Matrix S S ℝ := exp (t • R.Q)

theorem semigroup_zero : R.semigroup 0 = 1 := by
  simp [semigroup]

theorem semigroup_add (s t : ℝ) : R.semigroup (s + t) = R.semigroup s * R.semigroup t := by
  rw [semigroup, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl R.Q).smul_left s).smul_right t)]
  rfl

theorem hasDerivAt_semigroup (t : ℝ) (x y : S) :
    HasDerivAt (fun s => R.semigroup s x y) ((R.semigroup t * R.Q) x y) t := by
  open scoped Matrix.Norms.Operator in
  exact ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ x y)).hasFDerivAt
    (x := exp (t • R.Q))).comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) R.Q t)

theorem hasDerivAt_semigroup' (t : ℝ) (x y : S) :
    HasDerivAt (fun s => R.semigroup s x y) ((R.Q * R.semigroup t) x y) t := by
  open scoped Matrix.Norms.Operator in
  exact ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ x y)).hasFDerivAt
    (x := exp (t • R.Q))).comp_hasDerivAt t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) R.Q t)

theorem semigroup_row_sum (t : ℝ) (x : S) : ∑ y, R.semigroup t x y = 1 := by
  have hd : ∀ s, HasDerivAt (fun s => ∑ y, R.semigroup s x y) 0 s := by
    intro s
    have h := HasDerivAt.fun_sum (u := univ) fun y _ => R.hasDerivAt_semigroup s x y
    have h0 : ∑ y, (R.semigroup s * R.Q) x y = 0 := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp [← Finset.mul_sum, R.row_sum]
    rwa [h0] at h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  rw [hconst]
  simp [semigroup_zero, Matrix.one_apply]

private theorem exp_apply_nonneg {B : Matrix S S ℝ} (hB : ∀ u v, 0 ≤ B u v) (x y : S) :
    0 ≤ (exp B) x y := by
  open scoped Matrix.Norms.Operator in
  have hs := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ x y)).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) B)
  refine hasSum_le (fun n => ?_) hasSum_zero hs
  change 0 ≤ (((n.factorial : ℝ)⁻¹) • B ^ n) x y
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (Matrix.pow_apply_nonneg hB n x y)

theorem semigroup_nonneg {t : ℝ} (ht : 0 ≤ t) (x y : S) : 0 ≤ R.semigroup t x y := by
  set c : ℝ := ∑ z, R.rate z with hc
  set B : Matrix S S ℝ := R.Q + c • (1 : Matrix S S ℝ) with hB
  have hBnn : ∀ u v, 0 ≤ (t • B) u v := by
    intro u v
    rw [Matrix.smul_apply, smul_eq_mul]
    refine mul_nonneg ht ?_
    by_cases huv : u = v
    · subst huv
      have hle : R.rate u ≤ c :=
        Finset.single_le_sum (f := R.rate) (fun z _ => R.rate_nonneg z) (mem_univ u)
      have hq : R.Q u u = -R.rate u := by simp [rate]
      simp only [hB, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one, hq]
      linarith
    · simp only [hB, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne huv, smul_eq_mul,
        mul_zero, add_zero]
      exact R.off_diag_nonneg u v huv
  have hdecomp : t • R.Q = t • B + algebraMap ℝ (Matrix S S ℝ) (-(t * c)) := by
    rw [Algebra.algebraMap_eq_smul_one, hB, smul_add, smul_smul, add_assoc, ← add_smul]
    simp
  have hpos : (0 : ℝ) ≤ exp (-(t * c)) := by
    rw [← Real.exp_eq_exp_ℝ]
    exact (Real.exp_pos _).le
  have halg : exp (algebraMap ℝ (Matrix S S ℝ) (-(t * c))) =
      exp (-(t * c)) • (1 : Matrix S S ℝ) := by
    open scoped Matrix.Norms.Operator in
    exact (algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix S S ℝ) (-(t * c))).symm.trans
      (Algebra.algebraMap_eq_smul_one _)
  rw [semigroup, hdecomp, Matrix.exp_add_of_commute _ _ (Algebra.commute_algebraMap_right _ _),
    halg, mul_smul_comm, mul_one, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg hpos (exp_apply_nonneg hBnn x y)

noncomputable def semigroupChain (t : ℝ) (ht : 0 ≤ t) : FinChain S where
  P := R.semigroup t
  nonneg := R.semigroup_nonneg ht
  row_sum := R.semigroup_row_sum t

theorem semigroupChain_stepN (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (R.semigroupChain t ht).stepN n = R.semigroup (n * t) := by
  rw [FinChain.stepN, semigroup, mul_smul, Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  rfl

end Rhone.MarkovChain.RateChain
