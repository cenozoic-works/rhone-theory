/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederSource

/-!
# Covariances of Gaussian homologues and phenotype

Source: lande_arnold1983, p. 1212, eq. 5a. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem homologueZero_map (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    (gaussianParentLaw n G E).map (fun q => q.1.1) =
      multivariateGaussian 0 ((1/2:ℝ) • G) := by
  change (gaussianParentLaw n G E).map (Prod.fst ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_fst measurable_fst]
  simp [gaussianParentLaw]

theorem homologueOne_map (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    (gaussianParentLaw n G E).map (fun q => q.1.2) =
      multivariateGaussian 0 ((1/2:ℝ) • G) := by
  change (gaussianParentLaw n G E).map (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst]
  simp [gaussianParentLaw]

theorem environment_map (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) :
    (gaussianParentLaw n G E).map Prod.snd = multivariateGaussian 0 E := by
  simp [gaussianParentLaw]

theorem homologueZero_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q : GaussianParent n => q.1.1 i) 2
      (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E ((EuclideanSpace.proj i).comp (homologueZeroCLM n))).memLp_two

theorem homologueOne_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q : GaussianParent n => q.1.2 i) 2
      (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E ((EuclideanSpace.proj i).comp (homologueOneCLM n))).memLp_two

theorem environment_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q : GaussianParent n => q.2 i) 2
      (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E ((EuclideanSpace.proj i).comp
    (ContinuousLinearMap.snd ℝ (V n × V n) (V n)))).memLp_two

theorem homologueZero_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.1 i, fun q => q.1.1 j; gaussianParentLaw n G E] =
      G i j / 2 := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : V n))
    (hG.smul (by positivity : (0:ℝ) ≤ 1/2)) i j
  rw [← homologueZero_map n G E] at h
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem homologueOne_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.2 i, fun q => q.1.2 j; gaussianParentLaw n G E] =
      G i j / 2 := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : V n))
    (hG.smul (by positivity : (0:ℝ) ≤ 1/2)) i j
  rw [← homologueOne_map n G E] at h
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem environment_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hE : E.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => q.2 i, fun q => q.2 j; gaussianParentLaw n G E] =
      E i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : V n)) hE i j
  rw [← environment_map n G E] at h
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)] at h
  exact h

theorem homologues_cross_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.1 i, fun q => q.1.2 j; gaussianParentLaw n G E] = 0 := by
  let H := multivariateGaussian (0 : V n) ((1/2:ℝ) • G)
  have hmap : (gaussianParentLaw n G E).map Prod.fst = H.prod H := by
    simp [gaussianParentLaw, H]
  have hi : MemLp (fun x : V n => x i) 2 H :=
    (IsGaussian.hasGaussianLaw_id (μ := H)).map_fun (EuclideanSpace.proj i) |>.memLp_two
  have hj : MemLp (fun x : V n => x j) 2 H :=
    (IsGaussian.hasGaussianLaw_id (μ := H)).map_fun (EuclideanSpace.proj j) |>.memLp_two
  have h := covariance_fst_snd_prod hi hj
  rw [← hmap] at h
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)] at h
  exact h

theorem homologueZero_environment_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.1 i, fun q => q.2 j; gaussianParentLaw n G E] = 0 := by
  let H := multivariateGaussian (0 : V n) ((1/2:ℝ) • G)
  have hi : MemLp (fun x : V n => x i) 2 H :=
    (IsGaussian.hasGaussianLaw_id (μ := H)).map_fun (EuclideanSpace.proj i) |>.memLp_two
  have hj : MemLp (fun x : V n => x j) 2 (multivariateGaussian 0 E) :=
    (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian 0 E)).map_fun
      (EuclideanSpace.proj j) |>.memLp_two
  exact covariance_fst_snd_prod (hi.comp_fst H) hj

theorem homologueOne_environment_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.2 i, fun q => q.2 j; gaussianParentLaw n G E] = 0 := by
  let H := multivariateGaussian (0 : V n) ((1/2:ℝ) • G)
  have hi : MemLp (fun x : V n => x i) 2 H :=
    (IsGaussian.hasGaussianLaw_id (μ := H)).map_fun (EuclideanSpace.proj i) |>.memLp_two
  have hj : MemLp (fun x : V n => x j) 2 (multivariateGaussian 0 E) :=
    (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian 0 E)).map_fun
      (EuclideanSpace.proj j) |>.memLp_two
  exact covariance_fst_snd_prod (hi.comp_snd H) hj

open MeasureTheory ProbabilityTheory

theorem breedingValue_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q : GaussianParent n => gaussianBreedingValue q i) 2
      (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E ((EuclideanSpace.proj i).comp (breedingValueCLM n))).memLp_two

theorem centeredPhenotype_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q : GaussianParent n => (gaussianBreedingValue q + q.2) i) 2
      (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E
    ((EuclideanSpace.proj i).comp (centeredPhenotypeCLM n))).memLp_two

theorem breedingValue_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => gaussianBreedingValue q i,
      fun q => gaussianBreedingValue q j; gaussianParentLaw n G E] = G i j := by
  have h0 (k : Fin n) := homologueZero_coordinate_memLp n G E k
  have h1 (k : Fin n) := homologueOne_coordinate_memLp n G E k
  change cov[(fun q : GaussianParent n => q.1.1 i) + (fun q => q.1.2 i),
    (fun q => q.1.1 j) + (fun q => q.1.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_right ((h0 i).add (h1 i)) (h0 j) (h1 j),
    covariance_add_left (h0 i) (h1 i) (h0 j),
    covariance_add_left (h0 i) (h1 i) (h1 j),
    homologueZero_covariance n G E hG, homologueOne_covariance n G E hG,
    homologues_cross_covariance, covariance_comm (fun q : GaussianParent n => q.1.2 i),
    homologues_cross_covariance]
  ring

theorem breedingValue_environment_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    cov[fun q : GaussianParent n => gaussianBreedingValue q i,
      fun q => q.2 j; gaussianParentLaw n G E] = 0 := by
  change cov[(fun q : GaussianParent n => q.1.1 i) + (fun q => q.1.2 i),
    (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_left (homologueZero_coordinate_memLp n G E i)
      (homologueOne_coordinate_memLp n G E i) (environment_coordinate_memLp n G E j),
    homologueZero_environment_covariance, homologueOne_environment_covariance]
  simp

theorem centeredPhenotype_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hE : E.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => (gaussianBreedingValue q + q.2) i,
      fun q => (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] =
      (G + E) i j := by
  have hg (k : Fin n) := breedingValue_coordinate_memLp n G E k
  have he (k : Fin n) := environment_coordinate_memLp n G E k
  change cov[(fun q : GaussianParent n => gaussianBreedingValue q i) + (fun q => q.2 i),
    (fun q => gaussianBreedingValue q j) + (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_right ((hg i).add (he i)) (hg j) (he j),
    covariance_add_left (hg i) (he i) (hg j),
    covariance_add_left (hg i) (he i) (he j),
    breedingValue_covariance n G E hG, environment_covariance n G E hE,
    breedingValue_environment_covariance,
    covariance_comm (fun q : GaussianParent n => q.2 i), breedingValue_environment_covariance]
  simp

theorem breedingValue_centeredPhenotype_covariance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => gaussianBreedingValue q i,
      fun q => (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = G i j := by
  change cov[(fun q : GaussianParent n => gaussianBreedingValue q i),
    (fun q => gaussianBreedingValue q j) + (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_right (breedingValue_coordinate_memLp n G E i)
      (breedingValue_coordinate_memLp n G E j) (environment_coordinate_memLp n G E j),
    breedingValue_covariance n G E hG, breedingValue_environment_covariance, add_zero]

theorem homologueZero_centeredPhenotype_covariance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.1 i,
      fun q => (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = G i j / 2 := by
  have h0 (k : Fin n) := homologueZero_coordinate_memLp n G E k
  have h1 (k : Fin n) := homologueOne_coordinate_memLp n G E k
  have he (k : Fin n) := environment_coordinate_memLp n G E k
  change cov[(fun q : GaussianParent n => q.1.1 i),
    ((fun q => q.1.1 j) + (fun q => q.1.2 j)) + (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_right (h0 i) ((h0 j).add (h1 j)) (he j),
    covariance_add_right (h0 i) (h0 j) (h1 j), homologueZero_covariance n G E hG,
    homologues_cross_covariance, homologueZero_environment_covariance]
  simp

theorem homologueOne_centeredPhenotype_covariance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n => q.1.2 i,
      fun q => (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = G i j / 2 := by
  have h0 (k : Fin n) := homologueZero_coordinate_memLp n G E k
  have h1 (k : Fin n) := homologueOne_coordinate_memLp n G E k
  have he (k : Fin n) := environment_coordinate_memLp n G E k
  change cov[(fun q : GaussianParent n => q.1.2 i),
    ((fun q => q.1.1 j) + (fun q => q.1.2 j)) + (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_add_right (h1 i) ((h0 j).add (h1 j)) (he j),
    covariance_add_right (h1 i) (h0 j) (h1 j), homologueOne_covariance n G E hG,
    homologueOne_environment_covariance,
    covariance_comm (fun q : GaussianParent n => q.1.2 i), homologues_cross_covariance]
  simp

end Rhone.Statistics.GaussianBreeder
