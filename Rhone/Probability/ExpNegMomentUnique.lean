/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.ExpNegMoment
public import Rhone.Analysis.HausdorffMoment

/-! # A finite law on `[0, ∞]²` is determined by its joint Laplace transform at natural arguments -/

@[expose] public section

namespace Rhone.Probability.ExpNegMoment

open MeasureTheory Set Rhone.Analysis.ExpNegMoment
open scoped ENNReal

theorem eq_of_lintegral_pow_eq {α β : Measure ℝ} [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hα : α (Icc (0 : ℝ) 1)ᶜ = 0) (hβ : β (Icc (0 : ℝ) 1)ᶜ = 0)
    (h : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (x ^ n) ∂α = ∫⁻ x, ENNReal.ofReal (x ^ n) ∂β) :
    α = β := by
  have key : ∀ (ρ : Measure ℝ), ρ (Icc (0 : ℝ) 1)ᶜ = 0 → ∀ n : ℕ,
      ∫ x, x ^ n ∂ρ = (∫⁻ x, ENNReal.ofReal (x ^ n) ∂ρ).toReal := by
    intro ρ hρ n
    refine integral_eq_lintegral_of_nonneg_ae ?_ (measurable_id.pow_const n).aestronglyMeasurable
    filter_upwards [mem_ae_iff.2 hρ] with x hx using pow_nonneg hx.1 n
  exact Analysis.HausdorffMoment.eq_of_moments_eq hα hβ fun n => by rw [key α hα, key β hβ, h n]

noncomputable def expNegReal (t : ℝ≥0∞) : ℝ := (Analysis.ExpNegMoment.expNeg t).toReal

theorem expNegReal_mem_Icc (t : ℝ≥0∞) : expNegReal t ∈ Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one
        ((Analysis.ExpNegMoment.expNeg_le_one t).trans_eq ENNReal.ofReal_one.symm)⟩

theorem measurableEmbedding_expNegReal : MeasurableEmbedding expNegReal := by
  have hc : Continuous expNegReal :=
    ENNReal.continuousOn_toReal.comp_continuous Analysis.ExpNegMoment.continuous_expNeg
        Analysis.ExpNegMoment.expNeg_ne_top
  have hi : Function.Injective expNegReal := fun s t hst =>
    Analysis.ExpNegMoment.expNeg_injective
        ((ENNReal.toReal_eq_toReal_iff' (Analysis.ExpNegMoment.expNeg_ne_top s)
            (Analysis.ExpNegMoment.expNeg_ne_top t)).1 hst)
  exact (hc.isClosedEmbedding hi).measurableEmbedding

theorem ofReal_expNegReal_pow (t : ℝ≥0∞) (m : ℕ) :
    ENNReal.ofReal (expNegReal t ^ m) = Analysis.ExpNegMoment.expNeg t ^ m := by
  unfold expNegReal
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
      (Analysis.ExpNegMoment.expNeg_ne_top t)]

theorem map_expNegReal_compl_Icc {γ : Type*} [MeasurableSpace γ] (ρ : Measure γ)
    {f : γ → ℝ≥0∞} (hf : Measurable f) :
    (ρ.map fun p => expNegReal (f p)) (Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hm : Measurable fun p => expNegReal (f p) :=
    measurableEmbedding_expNegReal.measurable.comp hf
  rw [Measure.map_apply hm measurableSet_Icc.compl]
  have : (fun p => expNegReal (f p)) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ :=
    eq_empty_iff_forall_notMem.2 fun p hp => hp (expNegReal_mem_Icc _)
  rw [this, measure_empty]

theorem eq_of_lintegral_expNeg_pow_eq {μ ν : Measure (ℝ≥0∞ × ℝ≥0∞)} [IsFiniteMeasure μ]
    (h : ∀ m n : ℕ, ∫⁻ p, Analysis.ExpNegMoment.expNeg p.1 ^ m * Analysis.ExpNegMoment.expNeg p.2 ^
        n ∂μ =
      ∫⁻ p, Analysis.ExpNegMoment.expNeg p.1 ^ m * Analysis.ExpNegMoment.expNeg p.2 ^ n ∂ν) : μ =
          ν := by
  have huniv : μ univ = ν univ := by simpa using h 0 0
  have : IsFiniteMeasure ν := ⟨by rw [← huniv]; exact measure_lt_top μ _⟩
  have he := measurableEmbedding_expNegReal
  have hpow : ∀ n : ℕ, Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => Analysis.ExpNegMoment.expNeg p.2 ^ n := fun
      n =>
    (Analysis.ExpNegMoment.measurable_expNeg.comp measurable_snd).pow_const n
  have hfin : ∀ (ρ : Measure (ℝ≥0∞ × ℝ≥0∞)) [IsFiniteMeasure ρ] (n : ℕ),
      ∫⁻ p, Analysis.ExpNegMoment.expNeg p.2 ^ n ∂ρ ≠ ∞ := by
    intro ρ _ n
    refine (lt_of_le_of_lt
        (lintegral_mono fun p => pow_le_one₀ zero_le (Analysis.ExpNegMoment.expNeg_le_one _))
      ?_).ne
    rw [lintegral_one]
    exact measure_lt_top ρ _
  have hA : ∀ (n : ℕ) {A : Set ℝ}, MeasurableSet A →
      ∫⁻ p in (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' A, Analysis.ExpNegMoment.expNeg p.2 ^ n
          ∂μ =
        ∫⁻ p in (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' A, Analysis.ExpNegMoment.expNeg p.2 ^ n
            ∂ν := by
    intro n A hAm
    have hm1 : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1 := he.measurable.comp measurable_fst
    have := isFiniteMeasure_withDensity (hfin μ n)
    have := isFiniteMeasure_withDensity (hfin ν n)
    have hmom : ∀ (ρ : Measure (ℝ≥0∞ × ℝ≥0∞)) (m : ℕ),
        ∫⁻ x, ENNReal.ofReal (x ^ m)
            ∂(ρ.withDensity fun p => Analysis.ExpNegMoment.expNeg p.2 ^ n).map
          (fun p => expNegReal p.1) = ∫⁻ p, Analysis.ExpNegMoment.expNeg p.1 ^ m *
              Analysis.ExpNegMoment.expNeg p.2 ^ n ∂ρ := by
      intro ρ m
      have hpm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ m) :=
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const m)
      have hg : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => ENNReal.ofReal (expNegReal p.1 ^ m) :=
        ENNReal.measurable_ofReal.comp (hm1.pow_const m)
      rw [lintegral_map hpm hm1, lintegral_withDensity_eq_lintegral_mul _ (hpow n) hg]
      refine lintegral_congr fun p => ?_
      change Analysis.ExpNegMoment.expNeg p.2 ^ n * ENNReal.ofReal (expNegReal p.1 ^ m) = _
      rw [ofReal_expNegReal_pow, mul_comm]
    have heq : (μ.withDensity fun p => Analysis.ExpNegMoment.expNeg p.2 ^ n).map
        (fun p => expNegReal p.1) =
        (ν.withDensity fun p => Analysis.ExpNegMoment.expNeg p.2 ^ n).map
            (fun p => expNegReal p.1) :=
      eq_of_lintegral_pow_eq (map_expNegReal_compl_Icc _ measurable_fst)
        (map_expNegReal_compl_Icc _ measurable_fst) fun m => by rw [hmom μ m, hmom ν m, h m n]
    have : ((μ.withDensity fun p => Analysis.ExpNegMoment.expNeg p.2 ^ n).map fun p => expNegReal
        p.1) A =
        ((ν.withDensity fun p => Analysis.ExpNegMoment.expNeg p.2 ^ n).map fun p => expNegReal p.1)
            A := by
      rw [heq]
    rwa [Measure.map_apply hm1 hAm, Measure.map_apply hm1 hAm,
      withDensity_apply _ (hm1 hAm), withDensity_apply _ (hm1 hAm)] at this
  have hAB : ∀ {A B : Set ℝ}, MeasurableSet A → MeasurableSet B →
      μ ((fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.2) ⁻¹' B ∩
        (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' A) =
      ν ((fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.2) ⁻¹' B ∩
        (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' A) := by
    intro A B hAm hBm
    have hm1 : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1 := he.measurable.comp measurable_fst
    have hm2 : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.2 := he.measurable.comp measurable_snd
    set S := (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' A with hS
    have hmom : ∀ (ρ : Measure (ℝ≥0∞ × ℝ≥0∞)) (n : ℕ),
        ∫⁻ x, ENNReal.ofReal (x ^ n) ∂(ρ.restrict S).map (fun p => expNegReal p.2) =
          ∫⁻ p in S, Analysis.ExpNegMoment.expNeg p.2 ^ n ∂ρ := by
      intro ρ n
      have hpm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ n) :=
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const n)
      rw [lintegral_map hpm hm2]
      exact lintegral_congr fun p => ofReal_expNegReal_pow _ n
    have heq : (μ.restrict S).map (fun p => expNegReal p.2) =
        (ν.restrict S).map (fun p => expNegReal p.2) :=
      eq_of_lintegral_pow_eq (map_expNegReal_compl_Icc _ measurable_snd)
        (map_expNegReal_compl_Icc _ measurable_snd) fun n => by
          rw [hmom μ n, hmom ν n, hA n hAm]
    have : ((μ.restrict S).map fun p => expNegReal p.2) B =
        ((ν.restrict S).map fun p => expNegReal p.2) B := by
      rw [heq]
    rwa [Measure.map_apply hm2 hBm, Measure.map_apply hm2 hBm,
      Measure.restrict_apply (hm2 hBm), Measure.restrict_apply (hm2 hBm)] at this
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ huniv
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have hst : s ×ˢ t = (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.2) ⁻¹' (expNegReal '' t) ∩
      (fun p : ℝ≥0∞ × ℝ≥0∞ => expNegReal p.1) ⁻¹' (expNegReal '' s) := by
    ext p
    simp only [mem_prod, mem_inter_iff, mem_preimage, he.injective.mem_set_image]
    exact and_comm
  change μ (s ×ˢ t) = ν (s ×ˢ t)
  rw [hst]
  exact hAB (he.measurableSet_image.2 hs) (he.measurableSet_image.2 ht)

end Rhone.Probability.ExpNegMoment
