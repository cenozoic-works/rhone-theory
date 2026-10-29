/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBulmerMasks
public import Rhone.Statistics.GaussianBulmerSelection

/-!
# Gaussian-input diploid free-assortment moments

Source: bulmer1971, eq. (17), p. 206; bulmer1974, p. 282; turelli2017_infinitesimal, sec. 4, p. 48.
-/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder Probability.DiploidMarginalSelection
open scoped ENNReal

noncomputable def freelyAssortingGameteLaw (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) : Measure (V n) :=
  ((gaussianSelectedParentLaw n G E w m).prod (meiosisMaskLaw n)).map
    (fun p => freelyTransmitted p.1 p.2)

noncomputable def freelyAssortingOffspringLaw (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (w : V n → ℝ) (m : V n) : Measure (V n) :=
  ((freelyAssortingGameteLaw n G E w m).prod
    (freelyAssortingGameteLaw n G E w m)).map (fun p => p.1+p.2)

theorem transmitted_coordinate_memLp (n : ℕ) (μ : Measure (GaussianParent n))
    [IsProbabilityMeasure μ] (i : Fin n)
    (h0 : MemLp (fun q => q.1.1 i) 2 μ) (h1 : MemLp (fun q => q.1.2 i) 2 μ) :
    MemLp (fun p => freelyTransmitted p.1 p.2 i) 2 (μ.prod (meiosisMaskLaw n)) := by
  have hdom := ((h0.comp_fst (meiosisMaskLaw n)).norm).add
    ((h1.comp_fst (meiosisMaskLaw n)).norm)
  have hm : Measurable (fun p : GaussianParent n × (Fin n → Fin 2) =>
      freelyTransmitted p.1 p.2 i) := by
    exact (EuclideanSpace.proj i).measurable.comp (freelyTransmitted_measurable n)
  apply hdom.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    change ‖if p.2 i=0 then p.1.1.1 i else p.1.1.2 i‖ ≤ ‖p.1.1.1 i‖+‖p.1.1.2 i‖
    split
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _))

theorem transmitted_mean (n : ℕ) (μ : Measure (GaussianParent n))
    [IsProbabilityMeasure μ] (i : Fin n)
    (h0 : MemLp (fun q => q.1.1 i) 2 μ) (h1 : MemLp (fun q => q.1.2 i) 2 μ) :
    (∫ p, freelyTransmitted p.1 p.2 i ∂μ.prod (meiosisMaskLaw n)) =
      (∫ q, gaussianBreedingValue q i ∂μ)/2 := by
  rw [integral_prod _ ((transmitted_coordinate_memLp n μ i h0 h1).integrable (by simp))]
  simp_rw [freelyTransmitted_mask_mean]
  exact integral_div _ _

theorem transmitted_second (n : ℕ) (μ : Measure (GaussianParent n))
    [IsProbabilityMeasure μ] (i j : Fin n)
    (h0 : ∀ k, MemLp (fun q => q.1.1 k) 2 μ)
    (h1 : ∀ k, MemLp (fun q => q.1.2 k) 2 μ) :
    (∫ p, freelyTransmitted p.1 p.2 i * freelyTransmitted p.1 p.2 j
      ∂μ.prod (meiosisMaskLaw n)) =
    ((∫ q, gaussianBreedingValue q i * gaussianBreedingValue q j ∂μ) +
      if i=j then (∫ q, homologueDifference q i * homologueDifference q j ∂μ) else 0)/4 := by
  have hti := transmitted_coordinate_memLp n μ i (h0 i) (h1 i)
  have htj := transmitted_coordinate_memLp n μ j (h0 j) (h1 j)
  rw [integral_prod (fun p : GaussianParent n × (Fin n → Fin 2) =>
    freelyTransmitted p.1 p.2 i * freelyTransmitted p.1 p.2 j) (hti.integrable_mul htj)]
  simp_rw [freelyTransmitted_mask_second]
  rw [integral_div]
  have hB : ∀ k, MemLp (fun q => gaussianBreedingValue q k) 2 μ := fun k =>
    (h0 k).add (h1 k)
  have hD : ∀ k, MemLp (fun q => homologueDifference q k) 2 μ := fun k =>
    (h0 k).sub (h1 k)
  by_cases hij : i=j
  · simp only [hij, ↓reduceIte]
    have hiB : Integrable (fun q => gaussianBreedingValue q j * gaussianBreedingValue q j) μ :=
      (hB j).integrable_mul (hB j)
    have hiD : Integrable (fun q => homologueDifference q j * homologueDifference q j) μ :=
      (hD j).integrable_mul (hD j)
    rw [integral_add hiB hiD]
  · simp only [hij, ↓reduceIte, add_zero]

theorem freelyAssortingGamete_probability (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    IsProbabilityMeasure (freelyAssortingGameteLaw n G E w m) := by
  have := selectedParent_probability n G E w hw0 m
    (bounded_fitness_integrable n G E w hw hw0 C hwC m) hbar
  exact (Measure.isProbabilityMeasure_map_iff (freelyTransmitted_measurable n).aemeasurable).mpr
    inferInstance

theorem freelyAssortingGamete_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (i : Fin n) :
    MemLp (fun z => z i) 2 (freelyAssortingGameteLaw n G E w m) := by
  have := selectedParent_probability n G E w hw0 m
    (bounded_fitness_integrable n G E w hw hw0 C hwC m) hbar
  unfold freelyAssortingGameteLaw
  apply (memLp_map_measure_iff (by fun_prop)
    (freelyTransmitted_measurable n).aemeasurable).mpr
  exact transmitted_coordinate_memLp n _ i
    (selected_coordinate_memLp n G E w C hwC m hbar _
      (homologueZero_coordinate_memLp n G E i))
    (selected_coordinate_memLp n G E w C hwC m hbar _
      (homologueOne_coordinate_memLp n G E i))

theorem gaussian_input_gamete_covariance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (i j : Fin n) :
    cov[fun z => z i, fun z => z j; freelyAssortingGameteLaw n G E w m] =
      cov[fun q => gaussianBreedingValue q i, fun q => gaussianBreedingValue q j;
        gaussianSelectedParentLaw n G E w m]/4 + if i=j then G i i/4 else 0 := by
  let μ := gaussianSelectedParentLaw n G E w m
  have hprob : IsProbabilityMeasure μ := selectedParent_probability n G E w hw0 m
    (bounded_fitness_integrable n G E w hw hw0 C hwC m) hbar
  let := hprob
  have hgam : IsProbabilityMeasure (freelyAssortingGameteLaw n G E w m) :=
    freelyAssortingGamete_probability n G E w hw hw0 C hwC m hbar
  let := hgam
  have h0 : ∀ k, MemLp (fun q : GaussianParent n => q.1.1 k) 2 μ := fun k =>
    selected_coordinate_memLp n G E w C hwC m hbar _ (homologueZero_coordinate_memLp n G E k)
  have h1 : ∀ k, MemLp (fun q : GaussianParent n => q.1.2 k) 2 μ := fun k =>
    selected_coordinate_memLp n G E w C hwC m hbar _ (homologueOne_coordinate_memLp n G E k)
  have hB : ∀ k, MemLp (fun q => gaussianBreedingValue q k) 2 μ := fun k =>
    (h0 k).add (h1 k)
  have hmean (k : Fin n) : (∫ z, z k ∂freelyAssortingGameteLaw n G E w m) =
      (∫ q, gaussianBreedingValue q k ∂μ)/2 := by
    rw [freelyAssortingGameteLaw, integral_map (freelyTransmitted_measurable n).aemeasurable
      (by fun_prop)]
    exact transmitted_mean n μ k (h0 k) (h1 k)
  have hsecond : (∫ z, z i*z j ∂freelyAssortingGameteLaw n G E w m) =
      ((∫ q, gaussianBreedingValue q i*gaussianBreedingValue q j ∂μ) +
        if i=j then G i j else 0)/4 := by
    rw [freelyAssortingGameteLaw, integral_map (freelyTransmitted_measurable n).aemeasurable
      (by fun_prop)]
    rw [transmitted_second n μ i j h0 h1]
    rw [selected_difference_product n G E hG w hw hw0 m hbar]
  rw [covariance_eq_sub (freelyAssortingGamete_coordinate_memLp n G E w hw hw0 C hwC m hbar i)
    (freelyAssortingGamete_coordinate_memLp n G E w hw hw0 C hwC m hbar j)]
  simp only [Pi.mul_apply]
  rw [hsecond, hmean i, hmean j, covariance_eq_sub (hB i) (hB j)]
  simp only [Pi.mul_apply]
  by_cases hij : i=j
  · subst j; simp only [↓reduceIte]; ring
  · simp only [hij, ↓reduceIte]; ring

end Rhone.Statistics.GaussianBulmer
