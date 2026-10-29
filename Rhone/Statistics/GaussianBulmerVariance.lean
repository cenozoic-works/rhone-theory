/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBulmerGamete
public import Mathlib.Probability.Moments.Variance

/-!
# Gaussian-input diploid free-assortment moments

Source: bulmer1971, eq. (17), p. 206; bulmer1974, p. 282; turelli2017_infinitesimal, sec. 4, p. 48.
-/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder Probability.DiploidMarginalSelection
open scoped ENNReal

theorem random_mating_covariance (n : ℕ) (ν : Measure (V n)) [IsProbabilityMeasure ν]
    (i j : Fin n) (hi : MemLp (fun z => z i) 2 ν) (hj : MemLp (fun z => z j) 2 ν) :
    cov[fun z => z i, fun z => z j; (ν.prod ν).map (fun p => p.1+p.2)] =
      2*cov[fun z => z i, fun z => z j; ν] := by
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  change cov[(fun p : V n × V n => p.1 i)+(fun p => p.2 i),
    (fun p => p.1 j)+(fun p => p.2 j); ν.prod ν] = _
  have hif := hi.comp_fst ν
  have his := hi.comp_snd ν
  have hjf := hj.comp_fst ν
  have hjs := hj.comp_snd ν
  rw [covariance_add_right (hif.add his) hjf hjs,
    covariance_add_left hif his hjf, covariance_add_left hif his hjs,
    covariance_fst_snd_prod hi hj]
  have hf : cov[fun p : V n × V n => p.1 i, fun p => p.1 j; ν.prod ν] =
      cov[fun z => z i, fun z => z j; ν] := by
    rw [← covariance_map_fun (μ := ν.prod ν) (X := fun z : V n => z i)
      (Y := fun z => z j) (Z := Prod.fst) (by fun_prop) (by fun_prop) (by fun_prop)]
    simp
  have hs : cov[fun p : V n × V n => p.2 i, fun p => p.2 j; ν.prod ν] =
      cov[fun z => z i, fun z => z j; ν] := by
    rw [← covariance_map_fun (μ := ν.prod ν) (X := fun z : V n => z i)
      (Y := fun z => z j) (Z := Prod.snd) (by fun_prop) (by fun_prop) (by fun_prop)]
    simp
  rw [hf, hs, covariance_comm (fun p : V n × V n => p.2 i), covariance_fst_snd_prod hj hi]
  ring

theorem freelyAssortingOffspring_probability (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    IsProbabilityMeasure (freelyAssortingOffspringLaw n G E w m) := by
  have := freelyAssortingGamete_probability n G E w hw hw0 C hwC m hbar
  unfold freelyAssortingOffspringLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

theorem freelyAssortingOffspring_coordinate_memLp (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (i : Fin n) :
    MemLp (fun z => z i) 2 (freelyAssortingOffspringLaw n G E w m) := by
  have := freelyAssortingGamete_probability n G E w hw hw0 C hwC m hbar
  have hi := freelyAssortingGamete_coordinate_memLp n G E w hw hw0 C hwC m hbar i
  unfold freelyAssortingOffspringLaw
  apply (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr
  exact (hi.comp_fst _).add (hi.comp_snd _)

theorem gaussian_input_free_assortment_covariance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hC : 0 ≤ C) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (i j : Fin n) :
    cov[fun z => z i, fun z => z j; freelyAssortingOffspringLaw n G E w m] =
      cov[fun q => gaussianBreedingValue q i, fun q => gaussianBreedingValue q j;
        gaussianSelectedParentLaw n G E w m]/2 + if i=j then G i i/2 else 0 := by
  have _ := hE
  have _ := hC
  have := freelyAssortingGamete_probability n G E w hw hw0 C hwC m hbar
  rw [freelyAssortingOffspringLaw,
    random_mating_covariance n _ i j
      (freelyAssortingGamete_coordinate_memLp n G E w hw hw0 C hwC m hbar i)
      (freelyAssortingGamete_coordinate_memLp n G E w hw hw0 C hwC m hbar j),
    gaussian_input_gamete_covariance n G E hG w hw hw0 C hwC m hbar i j]
  split_ifs <;> ring

theorem gaussian_input_free_assortment_variance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hC : 0 ≤ C) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    Var[fun z => ∑ i, z i; freelyAssortingOffspringLaw n G E w m] =
      Var[fun q => ∑ i, gaussianBreedingValue q i;
        gaussianSelectedParentLaw n G E w m]/2 + (∑ i, G i i)/2 := by
  have := selectedParent_probability n G E w hw0 m
    (bounded_fitness_integrable n G E w hw hw0 C hwC m) hbar
  have := freelyAssortingOffspring_probability n G E w hw hw0 C hwC m hbar
  have ho : ∀ i, MemLp (fun z => z i) 2 (freelyAssortingOffspringLaw n G E w m) :=
    freelyAssortingOffspring_coordinate_memLp n G E w hw hw0 C hwC m hbar
  have hB : ∀ i, MemLp (fun q => gaussianBreedingValue q i) 2
      (gaussianSelectedParentLaw n G E w m) := fun i =>
    selected_coordinate_memLp n G E w C hwC m hbar _ (breedingValue_coordinate_memLp n G E i)
  rw [variance_fun_sum ho, variance_fun_sum hB]
  simp_rw [gaussian_input_free_assortment_covariance n G E hG hE w hw hw0 C hC hwC m hbar]
  simp [Finset.sum_add_distrib, Finset.sum_div]

end Rhone.Statistics.GaussianBulmer
