/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.FiniteMomentGap
public import Rhone.Statistics.FiniteBlockModel.UniformLift
public import Rhone.Statistics.CollapsedGenealogy.Encoding
public import Rhone.Statistics.ThreeSiteSeparator.PanSortedMoments

/-! # Monomial identities for the uniform-cherry duration observer -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator FiniteBlockModel
open DependentPairedTest

def otherPower (n : Fin 3 → ℕ) (q : Fin 3) : ℕ := ∑ i, if i = q then 0 else n i

theorem two_level_product (n : Fin 3 → ℕ) (q : Fin 3) (a b : ℝ) :
    (∏ i : Fin 3, (if i = q then a else b) ^ n i) = a ^ n q * b ^ otherPower n q := by
  fin_cases q <;>
    simp [Fin.prod_univ_three, Fin.sum_univ_three, otherPower, pow_add] <;> ring

def cherryCoordinate : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

theorem pair_means_coordinate (q i : Fin 3) (a b : ℝ) :
    pairMeans a b q i = if i = cherryCoordinate q then a else b := by
  fin_cases q <;> fin_cases i <;> simp [pairMeans, cherryCoordinate, Equiv.swap_apply_def]

theorem encoded_monomial {k : ℝ} (hk : 0 ≤ k) (n : Fin 3 → ℕ)
    (g : Joint) (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2) :
    (∏ i, (encode k g i).val ^ n i) =
      scaledDurationKernel k (n (cherryCoordinate g.2))
        (otherPower n (cherryCoordinate g.2)) g.1 := by
  simp_rw [encode_value hk g hg, pair_means_coordinate]
  exact two_level_product n (cherryCoordinate g.2) _ _

def encodedProbability (k : ℝ) (μ : Measure Joint) [IsProbabilityMeasure μ] :
    ProbabilityMeasure (Cube 3) :=
  ⟨μ.map (encode k), inferInstance⟩

theorem encoded_mono_integrable (k : ℝ) (n : Fin 3 → ℕ) (μ : Measure Joint)
    [IsFiniteMeasure μ] : Integrable (fun g => ∏ i, (encode k g i).val ^ n i) μ := by
  let f : Cube 3 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ∏ i, (x i).val ^ n i, by fun_prop⟩
  change Integrable (f ∘ encode k) μ
  exact (integrable_map_measure f.continuous.aestronglyMeasurable
    (encode_measurable k).aemeasurable).mp (f.integrable (μ.map (encode k)))

theorem uniform_lift_monomial {k : ℝ} (hk : 0 ≤ k) (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (hμ : ThreeTipSites.NonnegativeTimes μ) (n : Fin 3 → ℕ) :
    monoMoment n (encodedProbability k (uniformLift μ)) =
      ∑ q : Fin 3, (1 / 3 : ℝ) *
        ∫ t, scaledDurationKernel k (n q) (otherPower n q) t ∂μ := by
  change (∫ x : Cube 3, ∏ i, (x i).val ^ n i ∂(uniformLift μ).map (encode k)) = _
  have hf : Measurable (fun x : Cube 3 => ∏ i, (x i).val ^ n i) := by fun_prop
  rw [integral_map (encode_measurable k).aemeasurable hf.aestronglyMeasurable]
  rw [show uniformLift μ = μ.prod cherryLaw from rfl,
    integral_prod_symm _ (encoded_mono_integrable k n (uniformLift μ))]
  rw [integral_fintype Integrable.of_finite]
  conv_rhs =>
    rw [← cherryCoordinate.sum_comp (fun q : Fin 3 => (1 / 3 : ℝ) *
      ∫ t, scaledDurationKernel k (n q) (otherPower n q) t ∂μ)]
  apply Finset.sum_congr rfl
  intro q _
  rw [show cherryLaw.real {q} = (1 : ℝ) / 3 from law_measure_real_singleton cherryFinite q]
  change (1 / 3 : ℝ) * (∫ t, ∏ i, (encode k (t, q) i).val ^ n i ∂μ) = _
  congr 1
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  exact encoded_monomial hk n (t, q) ht

end Rhone.Statistics.WeakRegularSeparation
