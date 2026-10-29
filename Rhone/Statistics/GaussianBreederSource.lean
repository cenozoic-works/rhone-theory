/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian homologues, environment, and Mendelian source

Source: lande_arnold1983, pp. 1212–1213, eq. 5a-6b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.Norms.L2Operator RealInnerProductSpace
abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev GaussianParent (n : ℕ) := (V n × V n) × V n

noncomputable def gaussianParentLaw (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    Measure (GaussianParent n) :=
  ((multivariateGaussian 0 ((1 / 2 : ℝ) • G)).prod
    (multivariateGaussian 0 ((1 / 2 : ℝ) • G))).prod
      (multivariateGaussian 0 E)

def gaussianBreedingValue {n : ℕ} (q : GaussianParent n) : V n := q.1.1 + q.1.2
def gaussianPhenotype {n : ℕ} (m : V n) (q : GaussianParent n) : V n :=
  m + gaussianBreedingValue q + q.2

noncomputable def gaussianMeanFitness (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (m : V n) : ℝ :=
  ∫ q, w (gaussianPhenotype m q) ∂gaussianParentLaw n G E

noncomputable def gaussianSelectedParentLaw (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) :
    Measure (GaussianParent n) :=
  (ENNReal.ofReal (gaussianMeanFitness n G E w m))⁻¹ •
    (gaussianParentLaw n G E).withDensity
      (fun q => ENNReal.ofReal (w (gaussianPhenotype m q)))

def gaussianTransmittedHomologue {n : ℕ} (q : GaussianParent n) (b : Fin 2) : V n :=
  if b = 0 then q.1.1 else q.1.2

noncomputable def gaussianOffspringLaw (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) : Measure (V n) :=
  let sel := gaussianSelectedParentLaw n G E w m
  let coin := (PMF.uniformOfFintype (Fin 2)).toMeasure
  ((sel.prod sel).prod ((coin.prod coin).prod (multivariateGaussian 0 E))).map
    (fun p => m + gaussianTransmittedHomologue p.1.1 p.2.1.1 +
      gaussianTransmittedHomologue p.1.2 p.2.1.2 + p.2.2)

noncomputable def gaussianSelectionDifferential (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) : V n :=
  (∫ q, gaussianPhenotype m q ∂gaussianSelectedParentLaw n G E w m) - m

noncomputable def gaussianSelectionGradient (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) : V n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹
    (gaussianSelectionDifferential n G E w m)

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def homologueZeroCLM (n : ℕ) : GaussianParent n →L[ℝ] V n :=
  (ContinuousLinearMap.fst ℝ (V n) (V n)).comp
    (ContinuousLinearMap.fst ℝ (V n × V n) (V n))

def homologueOneCLM (n : ℕ) : GaussianParent n →L[ℝ] V n :=
  (ContinuousLinearMap.snd ℝ (V n) (V n)).comp
    (ContinuousLinearMap.fst ℝ (V n × V n) (V n))

def breedingValueCLM (n : ℕ) : GaussianParent n →L[ℝ] V n :=
  homologueZeroCLM n + homologueOneCLM n

def centeredPhenotypeCLM (n : ℕ) : GaussianParent n →L[ℝ] V n :=
  breedingValueCLM n + ContinuousLinearMap.snd ℝ (V n × V n) (V n)

instance gaussianParentLaw_isGaussian (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    IsGaussian (gaussianParentLaw n G E) := by
  unfold gaussianParentLaw
  infer_instance

theorem parentLinear_hasGaussianLaw (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : GaussianParent n →L[ℝ] F) : HasGaussianLaw L (gaussianParentLaw n G E) := by
  simpa using (IsGaussian.hasGaussianLaw_id (μ := gaussianParentLaw n G E)).map_fun L

theorem parentLinear_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : GaussianParent n →L[ℝ] F) :
    ∫ q, L q ∂gaussianParentLaw n G E = 0 := by
  have hzero (S : Matrix (Fin n) (Fin n) ℝ) (A : V n →L[ℝ] F) :
      ∫ x, A x ∂multivariateGaussian 0 S = 0 := by
    rw [A.integral_comp_id_comm IsGaussian.integrable_id]
    simp
  unfold gaussianParentLaw
  rw [integral_continuousLinearMap_prod IsGaussian.integrable_id IsGaussian.integrable_id,
    integral_continuousLinearMap_prod IsGaussian.integrable_id IsGaussian.integrable_id]
  change (∫ x, (L.comp (ContinuousLinearMap.inl ℝ (V n × V n) (V n))).comp
      (ContinuousLinearMap.inl ℝ (V n) (V n)) x ∂multivariateGaussian 0 ((1/2:ℝ) • G)) +
    (∫ x, (L.comp (ContinuousLinearMap.inl ℝ (V n × V n) (V n))).comp
      (ContinuousLinearMap.inr ℝ (V n) (V n)) x ∂multivariateGaussian 0 ((1/2:ℝ) • G)) +
    (∫ x, L.comp (ContinuousLinearMap.inr ℝ (V n × V n) (V n)) x
      ∂multivariateGaussian 0 E) = 0
  rw [hzero, hzero, hzero]
  simp

theorem breedingValue_hasGaussianLaw (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    HasGaussianLaw gaussianBreedingValue (gaussianParentLaw n G E) := by
  exact parentLinear_hasGaussianLaw n G E (breedingValueCLM n)

theorem centeredPhenotype_hasGaussianLaw (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    HasGaussianLaw (fun q => gaussianBreedingValue q + q.2) (gaussianParentLaw n G E) := by
  exact parentLinear_hasGaussianLaw n G E (centeredPhenotypeCLM n)

theorem breedingValue_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    ∫ q, gaussianBreedingValue q ∂gaussianParentLaw n G E = 0 :=
  parentLinear_integral n G E (breedingValueCLM n)

theorem centeredPhenotype_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    ∫ q, gaussianBreedingValue q + q.2 ∂gaussianParentLaw n G E = 0 :=
  parentLinear_integral n G E (centeredPhenotypeCLM n)

end Rhone.Statistics.GaussianBreeder
