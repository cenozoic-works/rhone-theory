/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableOnset
public import Rhone.Statistics.Identifiability.IntegrableExposureOnset
public import Rhone.Statistics.Identifiability.ThreeMigrationPolynomial

/-!
# The literal locally L1 migration-only three-state flow has the polynomial occupancy solution
-/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

def migrationParameterFrom (k : ℕ) (q : ℝ → ℝ) (a t : ℝ) : ℝ :=
  Real.exp (-(k + 2 : ℝ) * ∫ u in a..t, q u)

lemma migrationParameterFrom_ac (k : ℕ) (q : ℝ → ℝ) (hq : LocallyIntegrable q volume)
    (a t : ℝ) : AbsolutelyContinuousOnInterval (migrationParameterFrom k q a) a t := by
  have hH := (locallyIntegrable_interval q hq a t).absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp)
  exact ac_exp
    ((LipschitzWith.const (-(k + 2 : ℝ))).lipschitzOnWith.absolutelyContinuousOnInterval.fun_mul hH)

lemma migrationParameterFrom_derivative_ae (k : ℕ) (q : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) (a : ℝ) :
    ∀ᵐ t, HasDerivAt (migrationParameterFrom k q a)
      (-(k + 2 : ℝ) * q t * migrationParameterFrom k q a t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hq] with t ht
  have hh := (ht a).const_mul (-(k + 2 : ℝ))
  have he : HasDerivAt Real.exp
      (Real.exp (-(k + 2 : ℝ) * ∫ u in a..t, q u)) (-(k + 2 : ℝ) * ∫ u in a..t, q u) :=
    Real.hasDerivAt_exp _
  have hz : HasDerivAt (migrationParameterFrom k q a)
      (Real.exp (-(k + 2 : ℝ) * ∫ u in a..t, q u) * (-(k + 2 : ℝ) * q t)) t := by
    convert! he.comp t hh using 1
  apply hz.congr_deriv
  unfold migrationParameterFrom
  ring

lemma migrationRow_ac (k : ℕ) (z : ℝ → ℝ) {a b : ℝ}
    (hz : AbsolutelyContinuousOnInterval z a b) (i : ThreeState) :
    AbsolutelyContinuousOnInterval (fun t => migrationRow k (z t) i) a b := by
  have hconst (x : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => x) a b :=
    (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval
  have hz2 : AbsolutelyContinuousOnInterval (fun t => (z t)^2) a b := by
    simpa only [pow_two] using hz.fun_mul hz
  have hz3 : AbsolutelyContinuousOnInterval (fun t => (z t)^3) a b := by
    simpa only [pow_succ] using hz2.fun_mul hz
  have hp : AbsolutelyContinuousOnInterval (fun t => pairCollision k (z t)) a b := by
    simpa only [pairCollision, div_eq_mul_inv] using
      ((hconst 1).fun_add ((hconst (k + 1 : ℝ)).fun_mul hz2)).fun_mul
        (hconst ((k + 2 : ℝ)⁻¹))
  have ha : AbsolutelyContinuousOnInterval (fun t => tripleSame k (z t)) a b := by
    simpa only [tripleSame, div_eq_mul_inv] using
      (((hconst 1).fun_add ((hconst (3 * (k + 1 : ℝ))).fun_mul hz2)).fun_add
        ((hconst ((k : ℝ) * (k + 1 : ℝ))).fun_mul hz3)).fun_mul
          (hconst (((k + 2 : ℝ)^2)⁻¹))
  fin_cases i
  · exact ha
  · exact (hconst 3).fun_mul (hp.sub ha)
  · exact ((hconst 1).sub ((hconst 3).fun_mul hp)).fun_add ((hconst 2).fun_mul ha)

theorem migration_only_transition_row (k : ℕ) (q : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) (a t : ℝ) :
    inhomogeneousTransition (fun u => threeGenerator k 0 (q u)) a t 0 =
      migrationRow k (migrationParameterFrom k q a t) := by
  let z := fun u => migrationRow k (migrationParameterFrom k q a u)
  have hQ := preGenerator_locallyIntegrable k (fun _ => 0) q (locallyIntegrable_const 0) hq
  have h := finiteRow_integrable_homogeneous_eq_transition
    (fun u => threeGenerator k 0 (q u)) hQ z a t
    (fun i => migrationRow_ac k _ (migrationParameterFrom_ac k q hq a t) i) (by
      filter_upwards [migrationParameterFrom_derivative_ae k q hq a] with u hu _ i
      exact migrationRow_hasDerivAt k _ hu i)
  have hinit : z a = Pi.single 0 1 := by simp [z, migrationParameterFrom, migrationRow_initial]
  rw [hinit] at h
  ext i
  have he := congrFun h i
  simpa only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, z] using he.symm

end Rhone.Statistics.Identifiability.ThreeIntegrable
