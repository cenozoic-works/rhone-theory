/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Moments
public import Rhone.Statistics.DependentPairedTest.MeasureBridge

/-! # Explicit uniform-cherry lift; no arbitrary labelled spatial equivalence is asserted -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.FiniteBlockModel
open CollapsedGenealogy ThreeTipSites DependenceBudget DependentPairedTest

def cherryFinite : Law (Fin 3) where
  mass := fun _ => 1 / 3
  nonneg := fun _ => by norm_num
  total := by norm_num [Fin.sum_univ_three]

def cherryLaw : Measure (Fin 3) := lawMeasure cherryFinite

instance cherryLaw_probability : IsProbabilityMeasure cherryLaw := by
  unfold cherryLaw
  infer_instance

def uniformLift (μ : Measure (ℝ × ℝ)) : Measure Joint := μ.prod cherryLaw

instance uniformLift_probability (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (uniformLift μ) := by unfold uniformLift; infer_instance

theorem uniform_lift_projection (μ : Measure (ℝ × ℝ)) [SFinite μ] :
    (uniformLift μ).map Prod.fst = μ := by
  simp only [uniformLift, Measure.map_fst_prod, measure_univ, one_smul]

theorem uniform_lift_injective (μ ν : Measure (ℝ × ℝ)) [SFinite μ] [SFinite ν] :
    uniformLift μ = uniformLift ν ↔ μ = ν := by
  constructor
  · intro he
    have h := congrArg (Measure.map Prod.fst) he
    simpa only [uniform_lift_projection] using h
  · rintro rfl
    rfl

theorem uniform_lift_nonnegative (μ : Measure (ℝ × ℝ)) [SFinite μ]
    (hμ : NonnegativeTimes μ) : NonnegativeJoint (uniformLift μ) := by
  exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := cherryLaw)).ae hμ

theorem uniform_lift_internal_positive (μ : Measure (ℝ × ℝ)) [SFinite μ]
    (hμ : ∀ᵐ t ∂μ, 0 < t.2) : ∀ᵐ g ∂uniformLift μ, 0 < g.1.2 := by
  exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := cherryLaw)).ae hμ

end Rhone.Statistics.FiniteBlockModel
