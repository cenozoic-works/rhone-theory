/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.TraitGaussianDensity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Gaussian trait mutation-selection closure

Source: lande1975, p. 225, eq. 2–4. -/

@[expose] public section
noncomputable section
namespace Rhone.Dynamics.TraitBalance
open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal MeasureTheory

/-- Source: lande1975, p. 225, eq. 2–4. -/
def stabilizingFitness (S : ℝ≥0) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-z^2/(2*(S : ℝ))))

/-- Source: lande1975, p. 225, eq. 2–4. -/
def selectionMass (V S : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ z, stabilizingFitness S z ∂(gaussianReal 0 V)

/-- Source: lande1975, p. 225, eq. 2–4. -/
def selectedTraitLaw (V S : ℝ≥0) : Measure ℝ :=
  (selectionMass V S)⁻¹ • (gaussianReal 0 V).withDensity (stabilizingFitness S)

/-- Source: lande1975, p. 225, eq. 2–4. -/
def selectedVariance (V S : ℝ≥0) : ℝ≥0 := V*S/(V+S)

/-- Source: lande1975, p. 225, eq. 2–4. -/
def nextTraitLaw (V S M : ℝ≥0) : Measure ℝ :=
  (selectedTraitLaw V S) ∗ (gaussianReal 0 M)

/-- Source: lande1975, p. 225, eq. 2–4. -/
def nextVariance (V S M : ℝ≥0) : ℝ≥0 := selectedVariance V S + M

/-- Source: lande1975, p. 225, eq. 2–4. -/
private theorem weighted_trait_measure (V S : ℝ≥0) (hV : 0 < V) (hS : 0 < S) :
    (gaussianReal 0 V).withDensity (stabilizingFitness S) =
      ENNReal.ofReal (Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ)))) •
        gaussianReal 0 (selectedVariance V S) := by
  have hw : 0 < selectedVariance V S := by unfold selectedVariance; positivity
  have hf : Measurable (stabilizingFitness S) := by unfold stabilizingFitness; fun_prop
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hV),
    gaussianReal_of_var_ne_zero 0 (ne_of_gt hw),
    ← withDensity_mul volume (measurable_gaussianPDF 0 V) hf]
  have hpdf : gaussianPDF 0 V * stabilizingFitness S =
      ENNReal.ofReal (Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ)))) •
        gaussianPDF 0 (selectedVariance V S) := by
    funext z
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, gaussianPDF,
      stabilizingFitness, selectedVariance]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 V z),
      weighted_gaussian_density V S hV hS z,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [hpdf, withDensity_smul _ (measurable_gaussianPDF 0 (selectedVariance V S))]

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem selection_mass_formula (V S : ℝ≥0) (hV : 0 < V) (hS : 0 < S) :
    selectionMass V S = ENNReal.ofReal (Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ)))) := by
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ) (weighted_trait_measure V S hV hS)
  simpa [selectionMass, withDensity_apply, Measure.smul_apply] using h

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem selected_trait_gaussian (V S : ℝ≥0) (hV : 0 < V) (hS : 0 < S) :
    selectedTraitLaw V S = gaussianReal 0 (selectedVariance V S) := by
  have hc : ENNReal.ofReal (Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ)))) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  rw [selectedTraitLaw, weighted_trait_measure V S hV hS, selection_mass_formula V S hV hS,
    smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem selected_trait_probability (V S : ℝ≥0) (hV : 0 < V) (hS : 0 < S) :
    IsProbabilityMeasure (selectedTraitLaw V S) := by
  rw [selected_trait_gaussian V S hV hS]
  infer_instance

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem mutation_selected_trait_gaussian
    (V S M : ℝ≥0) (hV : 0 < V) (hS : 0 < S) :
    nextTraitLaw V S M = gaussianReal 0 (nextVariance V S M) := by
  rw [nextTraitLaw, selected_trait_gaussian V S hV hS, gaussianReal_conv_gaussianReal]
  simp only [zero_add, nextVariance]

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem gaussian_variance_equilibrium_iff
    (V S M : ℝ≥0) (hS : 0 < S) :
    nextVariance V S M = V ↔ (V : ℝ)^2 = (M : ℝ)*((V : ℝ)+(S : ℝ)) := by
  have hd : (V : ℝ)+(S : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hcoe : nextVariance V S M = V ↔
      (V : ℝ)*(S : ℝ)/((V : ℝ)+(S : ℝ))+(M : ℝ) = (V : ℝ) := by
    simp [nextVariance, selectedVariance, ← NNReal.coe_inj]
  rw [hcoe]
  constructor
  · intro h
    field_simp [hd] at h
    nlinarith
  · intro h
    field_simp [hd]
    nlinarith

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem gaussian_variance_equilibrium_unique
    (V S M : ℝ≥0) (hS : 0 < S) :
    nextVariance V S M = V ↔
      (V : ℝ) = ((M : ℝ)+Real.sqrt ((M : ℝ)^2+4*(M : ℝ)*(S : ℝ)))/2 := by
  rw [gaussian_variance_equilibrium_iff V S M hS]
  have hD : 0 ≤ (M : ℝ)^2+4*(M : ℝ)*(S : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hD
  have hsqrt0 := Real.sqrt_nonneg ((M : ℝ)^2+4*(M : ℝ)*(S : ℝ))
  constructor
  · intro h
    have hvm : (M : ℝ) ≤ (V : ℝ) := by
      by_cases hv : V = 0
      · subst V
        have : (M : ℝ) = 0 := by
          have hms : (M : ℝ)*(S : ℝ) = 0 := by simpa using h.symm
          exact (mul_eq_zero.mp hms).resolve_right (ne_of_gt (NNReal.coe_pos.mpr hS))
        simp_all
      · have hv' : 0 < (V : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
        nlinarith [mul_nonneg (NNReal.coe_nonneg M) (NNReal.coe_nonneg S)]
    have hroot : 2*(V : ℝ)-(M : ℝ) =
        Real.sqrt ((M : ℝ)^2+4*(M : ℝ)*(S : ℝ)) := by
      nlinarith [NNReal.coe_nonneg V]
    linarith
  · intro h
    nlinarith

end Rhone.Dynamics.TraitBalance
