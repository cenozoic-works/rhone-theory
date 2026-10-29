/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PositiveGammaTransforms
public import Rhone.Algebra.FinitePanelGeometry.FullSupportBarycenter

/-! # Exact positive common-order Gamma interpolation on arbitrary finite Laplace grids -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Rhone.Statistics.Identifiability.ErlangApproximation

lemma atomFeature_continuous {d : ℕ} (s : Fin d → ℝ) : Continuous
    (Algebra.Identifiability.ErlangApproximation.atomFeature s) := by
  unfold Algebra.Identifiability.ErlangApproximation.atomFeature
  fun_prop

lemma atomFeature_dist_le {d : ℕ} (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i)
    (x y : Algebra.Identifiability.ErlangApproximation.PositiveTime) : dist
        (Algebra.Identifiability.ErlangApproximation.atomFeature s x)
        (Algebra.Identifiability.ErlangApproximation.atomFeature s y) ≤ 1 := by
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hx : Real.exp (-s i * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs i, x.property])
  have hy : Real.exp (-s i * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs i, y.property])
  change |Real.exp (-s i * x) - Real.exp (-s i * y)| ≤ 1
  exact abs_le.mpr ⟨by linarith [Real.exp_pos (-s i * x)],
    by linarith [Real.exp_pos (-s i * y)]⟩

def boundedAtomFeature {d : ℕ} (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i) :
    Algebra.Identifiability.ErlangApproximation.PositiveTime →ᵇ (Fin d → ℝ) :=
  BoundedContinuousFunction.mkOfBound
      ⟨Algebra.Identifiability.ErlangApproximation.atomFeature s, atomFeature_continuous s⟩ 1
    (atomFeature_dist_le s hs)

lemma gamma_feature_integral {d : ℕ} (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (i : Fin d) :
    (∫ t, boundedAtomFeature s hs t ∂positiveGamma a r) i = (r / (r + s i)) ^ a := by
  let : IsProbabilityMeasure (positiveGamma a r) := positiveGamma_probability ha hr
  have hi := (boundedAtomFeature s hs).integrable (positiveGamma a r)
  have h := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).integral_comp_comm hi
  simp only [ContinuousLinearMap.proj_apply] at h
  rw [← h]
  exact positiveGamma_laplace ha hr (hs i)

theorem eventually_gamma_feature_match {d : ℕ} (s : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, ∃ (t : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ),
      (↑t : Set (Fin d → ℝ)) ⊆ range
          (Algebra.Identifiability.ErlangApproximation.powerFeature s n) ∧
      t.Nonempty ∧ t.card ≤ d+1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = (fun i => a / (a + s i)) := by
  let μ := positiveGamma 1 a
  let : IsProbabilityMeasure μ := positiveGamma_probability zero_lt_one ha
  let : μ.IsOpenPosMeasure := positiveGamma_openPos zero_lt_one ha
  let ν : ℕ → Algebra.Identifiability.ErlangApproximation.PositiveTime → Measure
      Algebra.Identifiability.ErlangApproximation.PositiveTime := fun n x =>
    positiveGamma (n+2 : ℕ) ((n+2 : ℕ) / (x : ℝ))
  let (n : ℕ) (x : Algebra.Identifiability.ErlangApproximation.PositiveTime) : IsProbabilityMeasure
      (ν n x) :=
    positiveGamma_probability (by positivity) (div_pos (by positivity) x.property)
  have hval (n : ℕ) (x : Algebra.Identifiability.ErlangApproximation.PositiveTime) :
      (∫ y, boundedAtomFeature s hs y ∂ν n x) =
          Algebra.Identifiability.ErlangApproximation.powerFeature s n x := by
    ext i
    rw [gamma_feature_integral s hs (by positivity) (div_pos (by positivity) x.property)]
    rw [Real.rpow_natCast]
    exact (Algebra.Identifiability.ErlangApproximation.powerFeature_as_rate s hs n x i).symm
  have hlim (x : Algebra.Identifiability.ErlangApproximation.PositiveTime) :
      Tendsto (fun n => ∫ y, boundedAtomFeature s hs y ∂ν n x) atTop
        (𝓝 (boundedAtomFeature s hs x)) := by
    simp_rw [hval]
    exact Algebra.Identifiability.ErlangApproximation.powerFeature_tendsto s x
  have h := Algebra.FinitePanelGeometry.boundedContinuous_expectation_approximants_exact_match
    (μ := μ) (boundedAtomFeature s hs) ν hlim
  have hm : (∫ x, boundedAtomFeature s hs x ∂μ) = fun i => a / (a + s i) := by
    ext i
    rw [gamma_feature_integral s hs zero_lt_one ha, Real.rpow_one]
  simpa only [hval, hm, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

theorem eventually_exponential_rate_match {d : ℕ} (s : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, ∃ (t : Finset (Fin d → ℝ)) (w r : (Fin d → ℝ) → ℝ),
      t.Nonempty ∧ t.card ≤ d+1 ∧ (∀ y ∈ t, 0 < w y) ∧ (∀ y ∈ t, 0 < r y) ∧
      ∑ y ∈ t, w y = 1 ∧
      ∀ i, ∑ y ∈ t, w y * (r y / (r y + s i)) ^ (n+2) = a / (a + s i) := by
  classical
  filter_upwards [eventually_gamma_feature_match s hs ha] with n hn
  obtain ⟨t,w,htr,hne,hcard,hpos,hws,heq⟩ := hn
  have hrep : ∀ y : t, ∃ x : Algebra.Identifiability.ErlangApproximation.PositiveTime,
      Algebra.Identifiability.ErlangApproximation.powerFeature s n x = (y : Fin d → ℝ) :=
    fun y => htr y.property
  choose x hx using hrep
  let r : (Fin d → ℝ) → ℝ := fun y =>
    if hy : y ∈ t then (n+2 : ℕ) / (x ⟨y,hy⟩ : ℝ) else 1
  refine ⟨t,w,r,hne,hcard,hpos,?_,hws,?_⟩
  · intro y hy
    simp only [r, dite_eq_left hy]
    exact div_pos (by positivity) (x ⟨y,hy⟩).property
  · intro i
    have hcomponent := congrArg (fun z : Fin d → ℝ => z i) heq
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomponent
    rw [← hcomponent]
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    simp only [r, dite_eq_left hy]
    rw [← Algebra.Identifiability.ErlangApproximation.powerFeature_as_rate s hs n (x ⟨y,hy⟩) i, hx]

end Rhone.Statistics.Identifiability.ErlangApproximation
