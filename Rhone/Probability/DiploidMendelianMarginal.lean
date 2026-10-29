/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.DiploidMarginalSelection
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Constructions.Pi
/-! # Freely assorting multilocus meiosis and its derived locus marginals -/

@[expose] public section
namespace Rhone.Probability.DiploidMarginalSelection
open MeasureTheory
open scoped ENNReal
noncomputable def meiosisMaskLaw (n : ℕ) : Measure (Fin n → Fin 2) :=
  Measure.pi (fun _ => (PMF.uniformOfFintype (Fin 2)).toMeasure)
instance (n : ℕ) : IsProbabilityMeasure (meiosisMaskLaw n) := by
  unfold meiosisMaskLaw; infer_instance
noncomputable def mendelianGameteLaw (n : ℕ) (μ : Measure (Fin n → ℝ))
    (W : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞) : Measure (Fin n → ℝ) :=
  ((selectedDiploidLaw μ W).prod (meiosisMaskLaw n)).map
    (fun p => fun i => if p.2 i = 0 then p.1.1 i else p.1.2 i)
theorem meiosisMaskLaw_eval (n : ℕ) (i : Fin n) :
    (meiosisMaskLaw n).map (fun m => m i) = (PMF.uniformOfFintype (Fin 2)).toMeasure :=
  (measurePreserving_eval (fun _ => (PMF.uniformOfFintype (Fin 2)).toMeasure) i).map_eq
theorem meiosisMaskLaw_lintegral (n : ℕ) (i : Fin n) (a b : ℝ≥0∞) :
    (∫⁻ m, (if m i = 0 then a else b) ∂meiosisMaskLaw n) =
      (2 : ℝ≥0∞)⁻¹*a+(2 : ℝ≥0∞)⁻¹*b := by
  calc
    _ = ∫⁻ j : Fin 2, (if j = 0 then a else b)
        ∂(meiosisMaskLaw n).map (fun m => m i) :=
      (lintegral_map (measurable_of_countable _)
        (measurable_pi_apply i)).symm
    _ = _ := by
      rw [meiosisMaskLaw_eval]
      have hp (j : Fin 2) : (PMF.uniformOfFintype (Fin 2)).toMeasure {j} =
          (2 : ℝ≥0∞)⁻¹ := by
        rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
          PMF.uniformOfFintype_apply, Fintype.card_fin]
        norm_num
      simp [lintegral_fintype, Fin.sum_univ_two, hp, mul_comm]
theorem mendelianGameteLaw_marginal (n : ℕ) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (W : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞)
    (hW : Measurable W) (hsym : ∀ a b, W (a, b) = W (b, a)) (i : Fin n) :
    (mendelianGameteLaw n μ W).map (fun a => a i) =
      ((meanViability μ W)⁻¹ • μ.withDensity (marginalViability μ W)).map (fun a => a i) := by
  rw [← mendelianHomologLaw_eq_marginal μ W hW hsym]
  apply Measure.ext_of_lintegral
  intro f hf
  have heval : Measurable (fun a : Fin n → ℝ => a i) := measurable_pi_apply i
  have hobs : Measurable (fun a : Fin n → ℝ => f (a i)) := hf.comp heval
  have hfirst : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 i)) :=
    hobs.comp measurable_fst
  have hsecond : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.2 i)) :=
    hobs.comp measurable_snd
  have hchoose : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
      fun j => if p.2 j = 0 then p.1.1 j else p.1.2 j) := by
    apply measurable_pi_iff.mpr
    intro j
    apply ((measurable_pi_apply j).comp measurable_fst.fst).ite
      (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
      ((measurable_pi_apply j).comp measurable_fst.snd)
  rw [lintegral_map hf heval, lintegral_map hf heval]
  rw [mendelianGameteLaw, lintegral_map hobs hchoose]
  rw [mendelianHomologLaw, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_map hobs measurable_fst,
    lintegral_map hobs measurable_snd]
  have hjoint : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
      f (if p.2 i = 0 then p.1.1 i else p.1.2 i)) := by
    simpa only [Function.comp_def] using hobs.comp hchoose
  rw [lintegral_prod _ hjoint.aemeasurable]
  have hinner (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∫⁻ m, f (if m i = 0 then p.1 i else p.2 i) ∂meiosisMaskLaw n) =
        (2 : ℝ≥0∞)⁻¹*f (p.1 i)+(2 : ℝ≥0∞)⁻¹*f (p.2 i) := by
    convert meiosisMaskLaw_lintegral n i (f (p.1 i)) (f (p.2 i)) using 1
    apply lintegral_congr
    intro m
    split <;> rfl
  change (∫⁻ p, ∫⁻ m, f (if m i = 0 then p.1 i else p.2 i) ∂meiosisMaskLaw n
    ∂selectedDiploidLaw μ W) = _
  simp_rw [hinner]
  have hhalf : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (2 : ℝ≥0∞)⁻¹*f (p.1 i)) := measurable_const.mul hfirst
  rw [lintegral_add_left hhalf,
    lintegral_const_mul _ hfirst,
    lintegral_const_mul _ hsecond]
  simp only [smul_eq_mul]
end Rhone.Probability.DiploidMarginalSelection
