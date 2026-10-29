/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycleBalances
public import Mathlib.Probability.Moments.Variance
/-! # A symmetric two-point haplotype law is stationary under zero mutation -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory GaussianHouseOfCards
open scoped ENNReal NNReal
noncomputable def symmetricTwoPointHaplotypeLaw (A : ℝ) : Measure (Fin 1 → ℝ) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (fun _ => A) +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (fun _ => -A)

theorem symmetricTwoPointHaplotypeLaw_probability (A : ℝ) :
    IsProbabilityMeasure (symmetricTwoPointHaplotypeLaw A) := by
  constructor
  simp only [symmetricTwoPointHaplotypeLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

private theorem law_integrable (A : ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    Integrable f (symmetricTwoPointHaplotypeLaw A) := by
  unfold symmetricTwoPointHaplotypeLaw
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac (by simp)).smul_measure (by norm_num)

private theorem law_integral (A : ℝ) (f : (Fin 1 → ℝ) → ℝ) :
    (∫ a, f a ∂symmetricTwoPointHaplotypeLaw A) =
      (f (fun _ => A)+f (fun _ => -A))/2 := by
  rw [symmetricTwoPointHaplotypeLaw, integral_add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  simp [integral_smul_measure]
  ring

theorem symmetricTwoPointHaplotypeLaw_second (A : ℝ) :
    (∫ a, (a (0 : Fin 1)) ^ 2 ∂symmetricTwoPointHaplotypeLaw A) = A ^ 2 := by
  rw [law_integral]
  ring

private theorem locus_marginal_equal (A S : ℝ) :
    Probability.DiploidMarginalSelection.marginalViability (symmetricTwoPointHaplotypeLaw A)
        (diploidGaussianViability 1 S)
      (fun _ => A) =
    Probability.DiploidMarginalSelection.marginalViability (symmetricTwoPointHaplotypeLaw A)
        (diploidGaussianViability 1 S)
      (fun _ => -A) := by
  simp only [Probability.DiploidMarginalSelection.marginalViability, symmetricTwoPointHaplotypeLaw,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  simp only [diploidGaussianViability, haploidTrait, gaussianFitness, Fin.sum_univ_one]
  ring_nf

private theorem selected_first_equal (A S : ℝ) (hS : 0 < S) :
    (Probability.DiploidMarginalSelection.selectedDiploidLaw (symmetricTwoPointHaplotypeLaw A)
        (diploidGaussianViability 1 S)).map
      Prod.fst = symmetricTwoPointHaplotypeLaw A := by
  have := symmetricTwoPointHaplotypeLaw_probability A
  have hW := diploidGaussianViability_measurable 1 S
  let c := Probability.DiploidMarginalSelection.marginalViability (symmetricTwoPointHaplotypeLaw A)
      (diploidGaussianViability 1 S)
    (fun _ => A)
  have hd : (symmetricTwoPointHaplotypeLaw A).withDensity
      (Probability.DiploidMarginalSelection.marginalViability (symmetricTwoPointHaplotypeLaw A)
          (diploidGaussianViability 1 S)) =
      c • symmetricTwoPointHaplotypeLaw A := by
    change ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (fun _ : Fin 1 => A) +
      (2 : ℝ≥0∞)⁻¹ • Measure.dirac (fun _ : Fin 1 => -A)).withDensity
        (Probability.DiploidMarginalSelection.marginalViability (symmetricTwoPointHaplotypeLaw A)
            (diploidGaussianViability 1 S)) = _
    rw [withDensity_add_measure,
      withDensity_smul_measure, withDensity_smul_measure,
      dirac_withDensity, dirac_withDensity, ← locus_marginal_equal A S]
    rw [symmetricTwoPointHaplotypeLaw]
    simp only [c, smul_add, smul_smul]
    rw [mul_comm ((2 : ℝ≥0∞)⁻¹)]
    rfl
  have hc : Probability.DiploidMarginalSelection.meanViability (symmetricTwoPointHaplotypeLaw A)
      (diploidGaussianViability 1 S) = c := by
    have he := congrArg (fun ν : Measure (Fin 1 → ℝ) => ν Set.univ) hd
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    rw [Probability.DiploidMarginalSelection.meanViability, lintegral_prod _ hW.aemeasurable]
    simpa [Probability.DiploidMarginalSelection.marginalViability] using he
  have hc0 : c ≠ 0 := by
    rw [← hc]
    exact diploidGaussianMean_ne_zero 1 S hS _
  have hct : c ≠ ⊤ := by
    have hb : c ≤ 1 := by
      dsimp [c, Probability.DiploidMarginalSelection.marginalViability]
      calc
        _ ≤ ∫⁻ _ : Fin 1 → ℝ, (1 : ℝ≥0∞) ∂symmetricTwoPointHaplotypeLaw A :=
          lintegral_mono (fun b => diploidGaussianViability_le_one 1 S hS _)
        _ = 1 := by simp
    exact ne_of_lt (hb.trans_lt (by simp))
  rw [Probability.DiploidMarginalSelection.selectedDiploidLaw_fst _ _ hW, hd, hc, smul_smul,
    ENNReal.inv_mul_cancel hc0 hct, one_smul]

private theorem gamete_equal (A S : ℝ) (hS : 0 < S) :
    Probability.DiploidMarginalSelection.mendelianGameteLaw 1 (symmetricTwoPointHaplotypeLaw A)
        (diploidGaussianViability 1 S) =
      symmetricTwoPointHaplotypeLaw A := by
  have := symmetricTwoPointHaplotypeLaw_probability A
  apply (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding.map_injective
  change (Probability.DiploidMarginalSelection.mendelianGameteLaw 1 _ _).map
      (fun a => a (0 : Fin 1)) =
    (symmetricTwoPointHaplotypeLaw A).map (fun a => a (0 : Fin 1))
  rw [Probability.DiploidMarginalSelection.mendelianGameteLaw_marginal _ _ _
      (diploidGaussianViability_measurable 1 S)
    (diploidGaussianViability_symm 1 S)]
  rw [← Probability.DiploidMarginalSelection.selectedDiploidLaw_fst _ _
      (diploidGaussianViability_measurable 1 S),
    selected_first_equal A S hS]

private theorem zero_increment_dirac (T : Fin 1 → ℝ≥0) :
    mutationIncrementLaw 1 (fun _ => 0) T = Measure.dirac 0 := by
  have hp (i : Fin 1) : IsProbabilityMeasure (locusIncrementLaw 0 (T i)) :=
    locusIncrementLaw_probability _ _ (by norm_num) (by norm_num)
  apply (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding.map_injective
  change (mutationIncrementLaw 1 _ _).map (fun a => a (0 : Fin 1)) =
    (Measure.dirac (0 : Fin 1 → ℝ)).map (fun a => a (0 : Fin 1))
  rw [mutationIncrementLaw,
    (measurePreserving_eval (fun i => locusIncrementLaw 0 (T i)) (0 : Fin 1)).map_eq]
  simp [locusIncrementLaw]

theorem symmetricTwoPointHaplotypeLaw_reflection (A : ℝ) :
    (symmetricTwoPointHaplotypeLaw A).map (fun a => -a) = symmetricTwoPointHaplotypeLaw A := by
  have hr : Measurable (fun a : Fin 1 → ℝ => -a) := by fun_prop
  rw [symmetricTwoPointHaplotypeLaw, Measure.map_add _ _ hr,
    Measure.map_smul _ hr.aemeasurable, Measure.map_smul _ hr.aemeasurable,
    Measure.map_dirac' hr, Measure.map_dirac' hr]
  have hneg : -(fun _ : Fin 1 => A) = (fun _ => -A) := rfl
  have hpos : -(fun _ : Fin 1 => -A) = (fun _ => A) := by funext i; simp
  rw [hneg, hpos, add_comm]

theorem symmetricTwoPointHaplotypeLaw_zero_mutation_stationary
    (A S : ℝ) (hS : 0 < S) (T : Fin 1 → ℝ≥0) :
    diploidGaussianLifecycleUpdate 1 S (fun _ => 0) T
      (symmetricTwoPointHaplotypeLaw A) = symmetricTwoPointHaplotypeLaw A := by
  have := symmetricTwoPointHaplotypeLaw_probability A
  rw [diploidGaussianLifecycleUpdate, gamete_equal A S hS, gaussianIncrementMutation,
    zero_increment_dirac T, Measure.prod_dirac,
    Measure.map_map (haplotypeAddition_measurable 1) (by fun_prop)]
  have he : (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => fun i => p.1 i+p.2 i) ∘
      (fun x : Fin 1 → ℝ => (x, 0)) = id := by funext a i; simp
  rw [he, Measure.map_id]

theorem symmetricTwoPointHaplotypeLaw_diploid_variance (A : ℝ) :
    ProbabilityTheory.variance
      (fun p => haploidTrait 1 p.1+haploidTrait 1 p.2)
      ((symmetricTwoPointHaplotypeLaw A).prod (symmetricTwoPointHaplotypeLaw A)) = 2 * A ^ 2 := by
  have := symmetricTwoPointHaplotypeLaw_probability A
  have h2 : Integrable (fun a : Fin 1 → ℝ => (haploidTrait 1 a) ^ 2)
      (symmetricTwoPointHaplotypeLaw A) := law_integrable A _
  have hm : MemLp (haploidTrait 1) 2 (symmetricTwoPointHaplotypeLaw A) :=
    (memLp_two_iff_integrable_sq (haploidTrait_measurable 1).aestronglyMeasurable).mpr h2
  have hsum : MemLp (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      haploidTrait 1 p.1+haploidTrait 1 p.2) 2
      ((symmetricTwoPointHaplotypeLaw A).prod (symmetricTwoPointHaplotypeLaw A)) :=
    (hm.comp_fst (symmetricTwoPointHaplotypeLaw A)).add
    (hm.comp_snd (symmetricTwoPointHaplotypeLaw A))
  rw [variance_eq_sub hsum]
  have hmean : (∫ p : (Fin 1 → ℝ) × (Fin 1 → ℝ), haploidTrait 1 p.1+haploidTrait 1 p.2
      ∂(symmetricTwoPointHaplotypeLaw A).prod (symmetricTwoPointHaplotypeLaw A)) = 0 := by
    rw [integral_add ((hm.integrable (by norm_num)).comp_fst _)
      ((hm.integrable (by norm_num)).comp_snd _)]
    rw [integral_fun_fst (haploidTrait 1), integral_fun_snd (haploidTrait 1), law_integral]
    simp [haploidTrait]
  change (∫ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
    (haploidTrait 1 p.1+haploidTrait 1 p.2) ^ 2
    ∂(symmetricTwoPointHaplotypeLaw A).prod (symmetricTwoPointHaplotypeLaw A)) - _ = _
  rw [hmean]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
  rw [integral_prod _ hsum.integrable_sq]
  have hi (a : Fin 1 → ℝ) :
      (∫ b : Fin 1 → ℝ, (haploidTrait 1 a+haploidTrait 1 b) ^ 2
        ∂symmetricTwoPointHaplotypeLaw A) =
      ((haploidTrait 1 a+A) ^ 2+(haploidTrait 1 a-A) ^ 2)/2 := by
    rw [law_integral]
    simp [haploidTrait, sub_eq_add_neg]
  simp_rw [hi]
  rw [law_integral]
  simp [haploidTrait]
  ring
end Rhone.MarkovChain.DiploidMarginalSelection
