/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.Specialization
public import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-! # Removing the monicity restriction -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem roots_integralNormalization (p : K[X]) (hp : p ≠ 0) :
    p.integralNormalization.roots = p.roots.map (p.leadingCoeff * ·) := by
  rw [← roots_smul_nonzero p.integralNormalization (leadingCoeff_ne_zero.mpr hp),
    leadingCoeff_smul_integralNormalization, roots_scaleRoots p (isUnit_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr hp))]

theorem splits_integralNormalization {p : K[X]} (hp : p ≠ 0) (hsplit : p.Splits) :
    p.integralNormalization.Splits := by
  apply Splits.of_dvd (hsplit.scaleRoots p.leadingCoeff)
    (scaleRoots_ne_zero hp p.leadingCoeff)
  exact ⟨C p.leadingCoeff, (integralNormalization_mul_C_leadingCoeff p).symm⟩

theorem isSplittingField_integralNormalization (p : K[X]) (hp : p ≠ 0)
    [IsSplittingField K L p] : IsSplittingField K L p.integralNormalization := by
  have hlc : algebraMap K L p.leadingCoeff ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K L)).mpr (leadingCoeff_ne_zero.mpr hp)
  constructor
  · rw [← integralNormalization_map (algebraMap K L) p hlc]
    exact splits_integralNormalization (map_ne_zero hp) (IsSplittingField.splits L p)
  · apply _root_.eq_top_iff.mpr
    rw [← IsSplittingField.adjoin_rootSet L p, Algebra.adjoin_le_iff]
    intro x hx
    change x ∈ Algebra.adjoin K (p.integralNormalization.rootSet L)
    have hr := aeval_eq_zero_of_mem_rootSet hx
    have hn : algebraMap K L p.leadingCoeff * x ∈
        Algebra.adjoin K (p.integralNormalization.rootSet L) := by
      apply Algebra.subset_adjoin
      apply (monic_integralNormalization hp).mem_rootSet.mpr
      exact integralNormalization_aeval_eq_zero hr
        (fun x hx => (algebraMap K L).injective (by simpa using hx))
    have h := (Algebra.adjoin K (p.integralNormalization.rootSet L)).mul_mem
      ((Algebra.adjoin K (p.integralNormalization.rootSet L)).algebraMap_mem
        p.leadingCoeff⁻¹) hn
    simpa only [map_inv₀, inv_mul_cancel_left₀ hlc] using h

theorem separable_integralNormalization {p : K[X]} (hsep : p.Separable) :
    p.integralNormalization.Separable := by
  classical
  have hp := hsep.ne_zero
  have : IsSplittingField K p.SplittingField p.integralNormalization :=
    isSplittingField_integralNormalization p hp
  apply (nodup_aroots_iff_of_splits (monic_integralNormalization hp).ne_zero
    (IsSplittingField.splits p.SplittingField p.integralNormalization)).mp
  rw [aroots_def, ← integralNormalization_map (algebraMap K p.SplittingField) p
    ((_root_.map_ne_zero (algebraMap K p.SplittingField)).mpr
      (leadingCoeff_ne_zero.mpr hp)), roots_integralNormalization _ (map_ne_zero hp)]
  exact (nodup_roots hsep.map).map (mul_right_injective₀
    (leadingCoeff_ne_zero.mpr (map_ne_zero hp)))

end Rhone.Algebra.GaloisSpecialization
