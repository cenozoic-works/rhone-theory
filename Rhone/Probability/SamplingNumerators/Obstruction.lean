/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Specialization
public import Rhone.Probability.SamplingNumerators.Point
public import Rhone.Algebra.DiagonalIrreducibility.Generic
public import Rhone.Algebra.BoundedDenominator

/-! # A degree-four denominator in the sampling probability at `(3,3)` -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Polynomial Algebra.DiagonalIrreducibility

theorem E33_on_slice :
    LinearAlgebra.Tridiag.E SamplingBivariate 3 3 1 (X - 1) (C X) = E33Theta := by
  rw [E33Theta_eq_E]
  apply Analysis.DenominatorEquation.E_indep_of_theta
  ring

theorem E33Theta_dvd_denominatorP : E33Theta ∣ denominatorP := by
  unfold denominatorP d33
  rw [E33_on_slice]
  exact dvd_mul_left _ _

theorem E33Theta_test_zero : paramEval (-10 : ℚ) 0 E33Theta = 0 := by
  rw [← E33_on_slice]
  change (paramEval (-10 : ℚ) 0).toRingHom
    (LinearAlgebra.Tridiag.E SamplingBivariate 3 3 1 (X - 1) (C X)) = 0
  rw [LinearAlgebra.Tridiag.E_map]
  convert E33_at_point using 1
  norm_num

theorem numeratorP_test_ne_zero : paramEval (-10 : ℚ) 0 numeratorP ≠ 0 := by
  rw [paramEval_numeratorP]
  norm_num only [show (-10 : ℚ) - 1 = -11 by norm_num]
  rw [samplingNumerator, E33_at_point, zero_mul, add_zero, n33_at_point]
  norm_num

theorem E33Theta_not_dvd_numeratorP : ¬ E33Theta ∣ numeratorP := by
  intro h
  have hd := map_dvd (paramEval (-10 : ℚ) 0).toRingHom h
  change paramEval (-10 : ℚ) 0 E33Theta ∣ paramEval (-10 : ℚ) 0 numeratorP at hd
  rw [E33Theta_test_zero, zero_dvd_iff] at hd
  exact numeratorP_test_ne_zero hd

abbrev SamplingCoefficientField := RatFunc ℚ
abbrev SamplingPolynomial := Polynomial SamplingCoefficientField
abbrev SamplingField := RatFunc SamplingCoefficientField

noncomputable def numeratorF : SamplingPolynomial :=
  numeratorP.map (algebraMap (Polynomial ℚ) SamplingCoefficientField)
noncomputable def denominatorF : SamplingPolynomial :=
  denominatorP.map (algebraMap (Polynomial ℚ) SamplingCoefficientField)

noncomputable def sampling33Value : SamplingField :=
  algebraMap SamplingPolynomial SamplingField numeratorF /
    algebraMap SamplingPolynomial SamplingField denominatorF

noncomputable def samplingA : SamplingField := 1
noncomputable def samplingB : SamplingField :=
  algebraMap SamplingPolynomial SamplingField (X - 1)
noncomputable def samplingRho : SamplingField :=
  algebraMap SamplingPolynomial SamplingField (C RatFunc.X)

theorem sampling33Value_eq_quotient :
    sampling33Value = samplingNumerator samplingA samplingB samplingRho /
      d33 samplingA samplingB samplingRho := by
  let f : SamplingBivariate →+* SamplingField :=
    (algebraMap SamplingPolynomial SamplingField).comp
      (mapRingHom (algebraMap (Polynomial ℚ) SamplingCoefficientField))
  have ha : f 1 = samplingA := map_one f
  have hb : f (X - 1) = samplingB := by simp [f, samplingB]
  have hr : f (C X) = samplingRho := by simp [f, samplingRho, RatFunc.algebraMap_X]
  have hn := samplingNumerator_map f f.map_rat_algebraMap 1 (X - 1) (C X)
  have hd := d33_map f 1 (X - 1) (C X)
  rw [ha, hb, hr] at hn hd
  change f numeratorP / f denominatorP = _
  exact congrArg₂ (fun x y : SamplingField => x / y) hn hd

theorem denominatorF_ne_zero : denominatorF ≠ 0 := by
  exact fun h => denominatorP_ne_zero
    ((Polynomial.map_injective _ (IsFractionRing.injective _ _)) (by simpa [denominatorF] using h))

theorem E33U_dvd_denominatorF : E33U ∣ denominatorF := by
  exact Polynomial.map_dvd (algebraMap (Polynomial ℚ) SamplingCoefficientField)
    E33Theta_dvd_denominatorP

theorem E33U_not_dvd_numeratorF : ¬ E33U ∣ numeratorF := by
  intro h
  exact E33Theta_not_dvd_numeratorP
    (E33Theta_primitive.dvd_of_fraction_map_dvd_fraction_map h)

theorem E33U_dvd_sampling33_denom : E33U ∣ sampling33Value.denom := by
  apply Rhone.Algebra.prime_dvd_denom denominatorF_ne_zero rfl E33U_irreducible.prime
  · exact E33U_dvd_denominatorF
  · exact E33U_not_dvd_numeratorF

theorem four_le_of_sampling33 {D : ℕ} {e : Algebra.Expr SamplingCoefficientField}
    (he : Algebra.DAdm samplingA samplingB samplingRho D e)
    (hv : Algebra.Expr.eval samplingA samplingB samplingRho e = sampling33Value) : 4 ≤ D := by
  have ha : Algebra.BoundedDen D samplingA := by
    simpa [samplingA] using (Algebra.boundedDen_of_poly D (1 : SamplingPolynomial))
  have hb : Algebra.BoundedDen D samplingB := Algebra.boundedDen_of_poly D (X - 1)
  have hr : Algebra.BoundedDen D samplingRho := Algebra.boundedDen_of_poly D (C RatFunc.X)
  have h := Algebra.natDegree_le_of_dvd_denom_eval ha hb hr he E33U_irreducible
    (by change E33U ∣ (Algebra.Expr.eval samplingA samplingB samplingRho e).denom
        rw [hv]; exact E33U_dvd_sampling33_denom)
  rwa [E33U_degree] at h

theorem no_degree_three_formula_sampling33 :
    ¬ ∃ e : Algebra.Expr SamplingCoefficientField,
      Algebra.DAdm samplingA samplingB samplingRho 3 e ∧
        Algebra.Expr.eval samplingA samplingB samplingRho e = sampling33Value := by
  rintro ⟨e, he, hv⟩
  have := four_le_of_sampling33 he hv
  omega

end Rhone.Probability.SamplingNumerators
