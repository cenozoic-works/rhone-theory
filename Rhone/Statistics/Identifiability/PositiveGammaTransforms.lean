/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Identifiability.ErlangTransformApproximation
public import Rhone.Statistics.Identifiability.TwoEventFluxLaw
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Positive-half-line Gamma measures and exact Laplace transforms -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.ErlangApproximation

def positiveVolume : Measure Algebra.Identifiability.ErlangApproximation.PositiveTime :=
    volume.comap Subtype.val

def positiveGamma (a r : ℝ) : Measure Algebra.Identifiability.ErlangApproximation.PositiveTime :=
  positiveVolume.withDensity (fun t => ENNReal.ofReal (gammaPDFReal a r t))

lemma positiveGamma_laplace {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ t : Algebra.Identifiability.ErlangApproximation.PositiveTime, Real.exp (-s*t) ∂positiveGamma
        a r) = (r/(r+s)) ^ a := by
  have hd : AEMeasurable
      (fun t : Algebra.Identifiability.ErlangApproximation.PositiveTime => gammaPDFReal a r t)
      positiveVolume :=
    ((measurable_gammaPDFReal a r).comp measurable_subtype_coe).aemeasurable
  rw [positiveGamma, TwoEventFluxLaw.integral_ofReal_density positiveVolume _ _ hd
    (ae_of_all _ fun t => gammaPDFReal_nonneg ha hr t)]
  change (∫ t : Algebra.Identifiability.ErlangApproximation.PositiveTime, gammaPDFReal a r t *
      Real.exp (-s*t)
    ∂volume.comap Subtype.val) = _
  have hsub : (∫ t : Algebra.Identifiability.ErlangApproximation.PositiveTime, gammaPDFReal a r t *
      Real.exp (-s*t)
      ∂volume.comap Subtype.val) =
      ∫ t in Ioi (0 : ℝ), gammaPDFReal a r t * Real.exp (-s*t) := by
    convert! (integral_subtype_comap (μ := (volume : Measure ℝ))
      (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun t : ℝ => gammaPDFReal a r t * Real.exp (-s*t))) using 1
  rw [hsub]
  have he : (fun t : ℝ => gammaPDFReal a r t * Real.exp (-s*t)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (r ^ a / Real.Gamma a) * (t ^ (a-1) * Real.exp (-((r+s)*t)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := (show (0 : ℝ) < t from ht).le
    simp only [gammaPDFReal, ite_eq_left ht0]
    have hh : Real.exp (-(r*t)) * Real.exp (-s*t) = Real.exp (-((r+s)*t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (r ^ a / Real.Gamma a) * t ^ (a-1) *
          (Real.exp (-(r*t)) * Real.exp (-s*t)) := by ring
      _ = _ := by rw [hh]; ring
  rw [integral_congr_ae he, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha (add_pos_of_pos_of_nonneg hr hs)]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  calc
    _ = (r ^ a * (1 / (r+s)) ^ a) * (Real.Gamma a / Real.Gamma a) := by ring
    _ = r ^ a * (1 / (r+s)) ^ a := by rw [div_self hG, mul_one]
    _ = (r/(r+s)) ^ a := by
      rw [← Real.mul_rpow hr.le (by positivity)]
      congr 1
      ring

lemma positiveGamma_probability {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (positiveGamma a r) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have h := positiveGamma_laplace ha hr (s := 0) le_rfl
  simpa [hr.ne', measureReal_def] using h

lemma positiveGamma_openPos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (positiveGamma a r).IsOpenPosMeasure := by
  let : positiveVolume.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioi.isOpenEmbedding_subtypeVal
  have hd : AEMeasurable
      (fun t : Algebra.Identifiability.ErlangApproximation.PositiveTime => ENNReal.ofReal
      (gammaPDFReal a r t))
      positiveVolume :=
    ((measurable_gammaPDFReal a r).comp measurable_subtype_coe).ennreal_ofReal.aemeasurable
  have hn : ∀ᵐ (t : Algebra.Identifiability.ErlangApproximation.PositiveTime) ∂positiveVolume,
      ENNReal.ofReal (gammaPDFReal a r t) ≠ 0 := by
    filter_upwards [] with t
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (gammaPDFReal_pos ha hr t.property))
  have habs : positiveVolume ≪ positiveGamma a r := withDensity_absolutelyContinuous' hd hn
  constructor
  intro U hU hne hzero
  exact (hU.measure_ne_zero positiveVolume hne) (habs hzero)

end Rhone.Statistics.Identifiability.ErlangApproximation
