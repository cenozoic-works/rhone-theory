/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeResidualMoments
/-!
# Scalar projections of the pedigree residual vector

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics
open scoped ENNReal
namespace Rhone.Statistics

noncomputable def locusResidualProjection {n : Nat} (P : Pedigree n) (m : Real)
    (t : Fin n → Real) (ω : (Fin n → Real) × (Fin n → Bool)) : Real :=
  ∑ i, t i * locusSegregationResidual P m ω.1 ω.2 i

theorem locus_projection_memLp {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (m : Real) (t : Fin n → Real) :
    MemLp (locusResidualProjection P m t) 2 (locusLaw n ν) := by
  exact memLp_finsetSum Finset.univ (fun i _ => (locus_residual_memLp P ν hν m i).const_mul (t i))

theorem locus_projection_mean_zero {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (t : Fin n → Real) :
    (∫ ω, locusResidualProjection P (∫ x, x ∂ν) t ω ∂(locusLaw n ν)) = 0 := by
  change (∫ ω : (Fin n → Real) × (Fin n → Bool),
    ∑ i, t i * locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i ∂(locusLaw n ν)) = 0
  rw [integral_finsetSum _ (fun i _ =>
    ((locus_residual_memLp P ν hν _ i).const_mul (t i)).integrable (by norm_num))]
  simp_rw [integral_const_mul, locus_residual_mean_zero P ν hν, mul_zero]
  simp

theorem locus_residual_covariance_diagonal {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i j : Fin n) :
    cov[fun ω => locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i,
      fun ω => locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 j; locusLaw n ν] =
      if i = j then segregationVariance P (Var[id; ν]) i else 0 := by
  simp only [covariance, locus_residual_mean_zero P ν hν, sub_zero]
  exact locus_residual_cross_diagonal P ν hν i j

theorem locus_projection_variance {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (t : Fin n → Real) :
    Var[locusResidualProjection P (∫ x, x ∂ν) t; locusLaw n ν] =
      ∑ i, (t i)^2 * segregationVariance P (Var[id; ν]) i := by
  classical
  change Var[fun ω => ∑ i, t i * locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i;
    locusLaw n ν] = _
  rw [variance_fun_sum (fun i => (locus_residual_memLp P ν hν _ i).const_mul (t i))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    locus_residual_covariance_diagonal P ν hν]
  apply Finset.sum_congr rfl
  intro i _
  simp [← mul_assoc, pow_two]
end Rhone.Statistics
