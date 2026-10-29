/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeResidual
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
/-!
# Fair-coin residual cancellation on finite pedigrees

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section

open MeasureTheory Rhone.Statistics Rhone.Combinatorics
open scoped ENNReal

namespace Rhone.Statistics

theorem coinLaw_eq_uniform (n : Nat) :
    (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ c (MeasurableSet.singleton _)]
  simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.uniformOfFintype_apply]
  simp [ENNReal.inv_pow]

theorem integral_coin_flip {n : Nat} (i : Fin n) (f : (Fin n → Bool) → Real) :
    (∫ c, f (flipInheritanceCoin i c)
      ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) =
    ∫ c, f c ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) := by
  rw [coinLaw_eq_uniform, PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, smul_eq_mul]
  exact (flipInheritanceCoin_involutive i).bijective.sum_comp (fun c : Fin n → Bool =>
    ((Fintype.card (Fin n → Bool) : ENNReal)⁻¹).toReal * f c)

theorem integral_coin_residual_zero {n : Nat} (P : Pedigree n) (i : Fin n)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) :
    (∫ c, locusSegregationResidual P m e c i
      ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) = 0 := by
  have h := integral_coin_flip i (fun c => locusSegregationResidual P m e c i)
  simp only [locusSegregationResidual_flip_neg P i parents hi] at h
  rw [integral_neg] at h
  linarith

theorem integral_coin_cross_residual_zero {n : Nat} (P : Pedigree n) (i j : Fin n)
    (hji : j < i) (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) :
    (∫ c, locusSegregationResidual P m e c j * locusSegregationResidual P m e c i
      ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) = 0 := by
  have h := integral_coin_flip i (fun c =>
    locusSegregationResidual P m e c j * locusSegregationResidual P m e c i)
  have hn : (fun c => locusSegregationResidual P m e (flipInheritanceCoin i c) j *
      locusSegregationResidual P m e (flipInheritanceCoin i c) i) =
      (fun c => -(locusSegregationResidual P m e c j * locusSegregationResidual P m e c i)) := by
    funext c
    rw [locusSegregationResidual_flip_neg P i parents hi]
    rw [show locusSegregationResidual P m e (flipInheritanceCoin i c) j =
        locusSegregationResidual P m e c j from
      locusSegregationResidual_before_current_coin P i j hji m e c (!(c i))]
    ring
  rw [hn, integral_neg] at h
  linarith
end Rhone.Statistics
