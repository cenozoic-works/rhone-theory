/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteBlockModel.UniformLift

/-! # Exact bridge between the explicit uniform-cherry lift and the duration observer -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.FiniteBlockModel
open CollapsedGenealogy ThreeTipSites DependentPairedTest

theorem cherry_real_singleton (q : Fin 3) : cherryLaw.real {q} = (1 : ℝ) / 3 := by
  exact law_measure_real_singleton cherryFinite q

theorem uniform_lift_mass {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (x : Panel K L) :
    jointMass π k (uniformLift μ) x = mass π k μ x := by
  let : IsFiniteMeasure (uniformLift μ) := by unfold uniformLift; infer_instance
  unfold jointMass mass
  rw [show uniformLift μ = μ.prod cherryLaw from rfl,
    integral_prod _ (fixed_integrable hK π hk (uniformLift μ) (uniform_lift_nonnegative μ hμ) x)]
  congr 1
  funext t
  rw [integral_fintype Integrable.of_finite]
  simp only [cherry_real_singleton, smul_eq_mul, ← Finset.mul_sum]
  rfl

theorem uniform_lift_sequence_law {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) : jointSequenceLaw π k (uniformLift μ) = law π k μ := by
  unfold jointSequenceLaw law
  congr 1
  funext x
  rw [uniform_lift_mass hK π hk μ hμ x]

end Rhone.Statistics.FiniteBlockModel
