/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeMigrationPolynomial
public import Rhone.Statistics.Identifiability.TimeVaryingProjectionDuhamel

/-! # The migration-only occupancy formulas equal the nonautonomous three-state flow -/

@[expose] public section

noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def migrationParameter (k : ℕ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(k + 2 : ℝ) * integratedClock q t)

lemma migrationParameter_derivative (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    HasDerivAt (migrationParameter k q)
      (-(k + 2 : ℝ) * q t * migrationParameter k q t) t := by
  have hH : HasDerivAt (integratedClock q) (q t) t :=
    intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 t)
      hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hh := hH.const_mul (-(k + 2 : ℝ))
  have he : HasDerivAt Real.exp
      (Real.exp (-(k + 2 : ℝ) * integratedClock q t)) (-(k + 2 : ℝ) * integratedClock q t) :=
    Real.hasDerivAt_exp _
  have hz : HasDerivAt (migrationParameter k q)
      (Real.exp (-(k + 2 : ℝ) * integratedClock q t) * (-(k + 2 : ℝ) * q t)) t := by
    convert! he.comp t hh using 1
  apply hz.congr_deriv
  unfold migrationParameter
  ring

lemma migrationParameter_zero (k : ℕ) (q : ℝ → ℝ) : migrationParameter k q 0 = 1 := by
  simp [migrationParameter, integratedClock]

lemma migrationParameter_positive (k : ℕ) (q : ℝ → ℝ) (t : ℝ) :
    0 < migrationParameter k q t := Real.exp_pos _

lemma migrationParameter_lt_one (k : ℕ) (q : ℝ → ℝ) {t : ℝ}
    (hQ : 0 < integratedClock q t) : migrationParameter k q t < 1 :=
  Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hQ)

theorem preRow_zero_coalescence (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    preRow k (fun _ => 0) q t = migrationRow k (migrationParameter k q t) := by
  let f := fun u => migrationRow k (migrationParameter k q u)
  have hf : ∀ u j, HasDerivAt (fun s => f s j)
      ((f u ᵥ* (fun u => threeGenerator k 0 (q u)) u - (0 : ThreeState → ℝ)) j) u := by
    intro u j
    simpa only [sub_zero] using
      migrationRow_hasDerivAt k (migrationParameter k q) (migrationParameter_derivative k q hq u) j
  have h := finiteRow_projection_duhamel (fun u => threeGenerator k 0 (q u))
    (preGenerator_continuous k (fun _ => 0) q continuous_const hq) f (fun _ => 0)
    continuous_const hf t
  have h0 : f 0 = Pi.single 0 (1 : ℝ) := by
    simp only [f, migrationParameter_zero, migrationRow_initial]
  simp only [Matrix.zero_vecMul, Pi.zero_apply, intervalIntegral.integral_zero] at h
  rw [h0] at h
  ext i
  have hi := congrFun h i
  simpa [f, preRow, Matrix.vecMul, dotProduct, Pi.single_apply] using hi.symm

theorem witness_zero_coalescence (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    witness k (fun _ => 0) q t =
      9 * (tripleSame k (migrationParameter k q t) -
        (pairCollision k (migrationParameter k q t))^2) := by
  simp only [witness, survival, preRow_zero_coalescence k q hq t,
    migrationRow_sum, migrationRow_weight]
  change 9 * tripleSame k (migrationParameter k q t) * 1 -
    (3 * pairCollision k (migrationParameter k q t))^2 = _
  ring

theorem witness_positive_silent_migration (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) {t : ℝ}
    (hQ : 0 < integratedClock q t) : 0 < witness k (fun _ => 0) q t := by
  rw [witness_zero_coalescence k q hq t]
  exact mul_pos (by norm_num) (tripleSame_sub_collision_sq_pos k
    (migrationParameter_positive k q t) (migrationParameter_lt_one k q hQ))

end Rhone.Statistics.Identifiability.ThreeTimeVarying
