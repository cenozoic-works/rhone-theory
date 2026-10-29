/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.CDFJointFunction
public import Rhone.Statistics.ThreeSiteSeparator.EnergyIntegrals

/-! # Closed integral formulas for the continuous sorted-iid joint CDF -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def cdfJointWeightedIntegral (p q : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x^p*(∫ y in (0 : ℝ)..1, y^q*cdfJointFunction F x y)

def cdfCrossIntegral (p q : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x^p*(F x)^2*weightedPrimitive q F x

lemma cdfJointWeighted_expansion {F : ℝ → ℝ} (hF : Continuous F) (p q : ℕ) :
    cdfJointWeightedIntegral p q F =
      (3/2 : ℝ)*cdfCrossIntegral p q F -
        (1/2 : ℝ)*weightedPrimitive p (weightedPrimitive q (fun x => (F x)^3)) 1 +
        (1/((q : ℝ)+1))*(weightedPrimitive p (fun x => (F x)^3) 1 -
          weightedPrimitive (p+q+1) (fun x => (F x)^3) 1) := by
  have he : cdfJointWeightedIntegral p q F =
      ∫ x in (0 : ℝ)..1, (3/2 : ℝ)*(x^p*(F x)^2*weightedPrimitive q F x) -
        (1/2 : ℝ)*(x^p*weightedPrimitive q (fun y => (F y)^3) x) +
        (1/((q : ℝ)+1))*(x^p*(F x)^3-x^(p+q+1)*(F x)^3) := by
    unfold cdfJointWeightedIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [cdfJointFunction_inner_integral hF q hx]
    simp only [pow_add, pow_one]
    ring
  rw [he, integral_three_terms (by fun_prop) (by fun_prop) (by fun_prop),
    intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ => x^p*(F x)^3) by fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ => x^(p+q+1)*(F x)^3) by fun_prop).intervalIntegrable _ _)]
  rfl

lemma cdfJointWeighted_reduction {F : ℝ → ℝ} (hF : Continuous F) (p q : ℕ) :
    ((p : ℝ)+1)*((q : ℝ)+1)*cdfJointWeightedIntegral p q F =
      (3*((p : ℝ)+1)*((q : ℝ)+1)/2)*cdfCrossIntegral p q F -
        (((q : ℝ)+1)/2)*weightedPrimitive q (fun x => (F x)^3) 1 +
        ((p : ℝ)+1)*weightedPrimitive p (fun x => (F x)^3) 1 +
        (((q : ℝ)+1)/2-((p : ℝ)+1))*weightedPrimitive (p+q+1) (fun x => (F x)^3) 1 := by
  have hp : (p : ℝ)+1 ≠ 0 := by positivity
  have hq : (q : ℝ)+1 ≠ 0 := by positivity
  have hj := weighted_integral_identity q p (show Continuous (fun x => (F x)^3) by fun_prop)
  change ((p : ℝ)+1)*weightedPrimitive p (weightedPrimitive q (fun x => (F x)^3)) 1 =
    weightedPrimitive q (fun x => (F x)^3) 1 -
      weightedPrimitive (p+q+1) (fun x => (F x)^3) 1 at hj
  have he : weightedPrimitive p (weightedPrimitive q (fun x => (F x)^3)) 1 =
      (weightedPrimitive q (fun x => (F x)^3) 1 -
        weightedPrimitive (p+q+1) (fun x => (F x)^3) 1)/((p : ℝ)+1) := by
    apply (eq_div_iff hp).mpr
    nlinarith [hj]
  rw [cdfJointWeighted_expansion hF, he]
  field_simp
  ring

end Rhone.Statistics.ThreeSiteSeparator
