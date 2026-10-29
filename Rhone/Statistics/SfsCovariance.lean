/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsCovariancePotential
public import Rhone.Statistics.SfsVariance
public import Rhone.Statistics.SfsLinearStatistics
public import Mathlib.Probability.Moments.Covariance

/-!
# Covariances of the marked Kingman site frequency spectrum and Fay-Wu variances

Source: fu1995, eq. (1)–(3), pp. 174–175; durrett2008, Thm 2.2. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

open Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

private theorem pi_poisson_integral_weighted_count_mul' {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (w v : ι → ℝ) :
    ∫ x : ι → ℕ, (∑ i, w i * (x i : ℝ)) * (∑ i, v i * (x i : ℝ))
      ∂Measure.pi (fun j => poissonMeasure (r j)) =
    (∑ i, w i * r i) * (∑ i, v i * r i) + ∑ i, w i * v i * r i := by
  have hw := pi_poisson_integral_weighted_count_sq r w
  have hv := pi_poisson_integral_weighted_count_sq r v
  have hs := pi_poisson_integral_weighted_count_sq r (fun i => w i + v i)
  have iw := pi_poisson_integrable_weighted_count_sq r w
  have iv := pi_poisson_integrable_weighted_count_sq r v
  have is := pi_poisson_integrable_weighted_count_sq r (fun i => w i + v i)
  have isw : Integrable (fun x : ι → ℕ => (∑ i, (w i + v i) * (x i : ℝ)) ^ 2 -
      (∑ i, w i * (x i : ℝ)) ^ 2) (Measure.pi (fun j => poissonMeasure (r j))) := is.sub iw
  have he : (fun x : ι → ℕ => (∑ i, w i * (x i : ℝ)) * (∑ i, v i * (x i : ℝ))) =
      fun x => (1 / 2 : ℝ) * (((∑ i, (w i + v i) * (x i : ℝ)) ^ 2 -
        (∑ i, w i * (x i : ℝ)) ^ 2) - (∑ i, v i * (x i : ℝ)) ^ 2) := by
    funext x
    have hx : ∑ i, (w i + v i) * (x i : ℝ) =
        ∑ i, w i * (x i : ℝ) + ∑ i, v i * (x i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hx]
    ring
  have e1 : ∑ i, (w i + v i) * (r i : ℝ) = ∑ i, w i * (r i : ℝ) + ∑ i, v i * (r i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (w i + v i) ^ 2 * (r i : ℝ) =
      ∑ i, w i ^ 2 * (r i : ℝ) + ∑ i, v i ^ 2 * (r i : ℝ) +
        2 * ∑ i, w i * v i * (r i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he, integral_const_mul, integral_sub isw iv, integral_sub is iw, hs, hw, hv, e1, e2]
  ring

theorem integral_kingmanBranchMutationKernel_sfs_mul (n : ℕ) {i j : ℕ} (hij : i ≠ j)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanSfs n i (h, x) * markedKingmanSfs n j (h, x)
      ∂kingmanBranchMutationKernel n θ h =
      ((θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n i) h) *
        ((θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n j) h) := by
  simp_rw [markedKingmanSfs_eq_weighted]
  change (∫ x : KingmanMutationBranch n → ℕ,
    (∑ b : KingmanMutationBranch n, (if b.2.card = i then (1 : ℝ) else 0) * (x b : ℝ)) *
      (∑ b : KingmanMutationBranch n, (if b.2.card = j then (1 : ℝ) else 0) * (x b : ℝ))
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  have hz : ∑ b : KingmanMutationBranch n, (if b.2.card = i then (1 : ℝ) else 0) *
      (if b.2.card = j then (1 : ℝ) else 0) * (kingmanBranchMutationRate n θ h b : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : b.2.card = i
    · have h2 : b.2.card ≠ j := fun h2 => hij (h1.symm.trans h2)
      rw [ite_eq_right h2, mul_zero, zero_mul]
    · rw [ite_eq_right h1, zero_mul, zero_mul]
  rw [pi_poisson_integral_weighted_count_mul', hz, add_zero,
    sum_kingmanBranchMutationRate_blockWeight n θ h
      (fun B => if B.card = i then (1 : ℝ) else 0),
    sum_kingmanBranchMutationRate_blockWeight n θ h
      (fun B => if B.card = j then (1 : ℝ) else 0)]
  rfl

theorem memLp_two_markedKingmanSfs (n i : ℕ) (θ : ℝ≥0) :
    MemLp (markedKingmanSfs n i) 2 (markedKingmanLaw n θ) :=
  (memLp_two_iff_integrable_sq (measurable_markedKingmanSfs n i).aestronglyMeasurable).2
    (integrable_markedKingmanSfs_sq n i θ)

theorem integrable_markedKingmanSfs_mul (n i j : ℕ) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanSfs n i x * markedKingmanSfs n j x)
      (markedKingmanLaw n θ) :=
  (memLp_two_markedKingmanSfs n i θ).integrable_mul (memLp_two_markedKingmanSfs n j θ)

theorem markedKingmanSfs_mul_mean_of_lt {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j < n)
    (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x * markedKingmanSfs n j x ∂markedKingmanLaw n θ =
      (fuSigma n i j + 1 / ((i : ℝ) * (j : ℝ))) * (θ : ℝ) ^ 2 := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanSfs_mul n i j θ)]
  simp_rw [integral_kingmanBranchMutationKernel_sfs_mul n hij.ne θ]
  have he : (fun h : KingmanMutationHistory n =>
      ((θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n i) h) *
        ((θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n j) h)) =
      fun h => ((θ : ℝ) / 2) ^ 2 * (kingmanFiniteReward n (sfsBlockCount n i) h *
        kingmanFiniteReward n (sfsBlockCount n j) h) := by
    funext h
    ring
  rw [he, integral_const_mul, integral_kingmanFiniteReward_sfsBlockCount_mul hi hij hjn]
  ring

/-- Source: fu1995, eq. (31), p. 187. -/
theorem markedKingmanSfs_mul_mean {n i j : ℕ} (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j)
    (hjn : j < n) (hij : i ≠ j) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x * markedKingmanSfs n j x ∂markedKingmanLaw n θ =
      (fuSigma n i j + 1 / ((i : ℝ) * (j : ℝ))) * (θ : ℝ) ^ 2 := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact markedKingmanSfs_mul_mean_of_lt hi hlt hjn θ
  · simp_rw [mul_comm (markedKingmanSfs n i _) (markedKingmanSfs n j _)]
    rw [markedKingmanSfs_mul_mean_of_lt hj hgt hin θ, fuSigma_comm n j i,
      mul_comm (j : ℝ) (i : ℝ)]

/-- Source: fu1995, eq. (1)–(3), pp. 174–175. -/
theorem markedKingmanSfs_covariance {n i j : ℕ} (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j)
    (hjn : j < n) (θ : ℝ≥0) :
    cov[markedKingmanSfs n i, markedKingmanSfs n j; markedKingmanLaw n θ] =
      (if i = j then (θ : ℝ) / i else 0) + fuSigma n i j * (θ : ℝ) ^ 2 := by
  by_cases h : i = j
  · subst h
    rw [covariance_self (measurable_markedKingmanSfs n i).aemeasurable,
      markedKingmanSfs_variance hi hin θ, fuSigma_self, ite_eq_left rfl]
  · rw [covariance_eq_sub (memLp_two_markedKingmanSfs n i θ) (memLp_two_markedKingmanSfs n j θ)]
    change (∫ x, markedKingmanSfs n i x * markedKingmanSfs n j x ∂markedKingmanLaw n θ) -
      (∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ) *
        (∫ x, markedKingmanSfs n j x ∂markedKingmanLaw n θ) = _
    rw [markedKingmanSfs_mul_mean hi hin hj hjn h θ, markedKingmanSfs_mean hi hin θ,
      markedKingmanSfs_mean hj hjn θ, ite_eq_right h]
    have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
    ring

/-- Source: fu1995, p. 175, eq. (1), p. 174; durrett2008, eq. (2.27)–(2.28). -/
theorem markedKingman_linear_sfs_variance (n : ℕ) (w : ℕ → ℝ) (θ : ℝ≥0) :
    ProbabilityTheory.variance
        (fun x => ∑ i ∈ Icc 1 (n - 1), w i * markedKingmanSfs n i x) (markedKingmanLaw n θ) =
      (θ : ℝ) * ∑ i ∈ Icc 1 (n - 1), w i ^ 2 / (i : ℝ) +
        (θ : ℝ) ^ 2 * ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1), w i * w j * fuSigma n i j := by
  have hlp : ∀ i, MemLp (fun x => w i * markedKingmanSfs n i x) 2 (markedKingmanLaw n θ) :=
    fun i => (memLp_two_markedKingmanSfs n i θ).const_mul (w i)
  have hmeas : AEMeasurable (fun x => ∑ i ∈ Icc 1 (n - 1), w i * markedKingmanSfs n i x)
      (markedKingmanLaw n θ) :=
    (Finset.measurable_sum _ fun i _ =>
      (measurable_markedKingmanSfs n i).const_mul (w i)).aemeasurable
  have hterm : ∀ i ∈ Icc 1 (n - 1), ∀ j ∈ Icc 1 (n - 1),
      cov[fun x => w i * markedKingmanSfs n i x, fun x => w j * markedKingmanSfs n j x;
        markedKingmanLaw n θ] =
      w i * w j * ((if i = j then (θ : ℝ) / i else 0) + fuSigma n i j * (θ : ℝ) ^ 2) := by
    intro i hi j hj
    rw [Finset.mem_Icc] at hi hj
    rw [covariance_const_mul_left, covariance_const_mul_right,
      markedKingmanSfs_covariance hi.1 (by omega) hj.1 (by omega) θ]
    ring
  have hsplit : ∀ i ∈ Icc 1 (n - 1),
      ∑ j ∈ Icc 1 (n - 1),
        w i * w j * ((if i = j then (θ : ℝ) / i else 0) + fuSigma n i j * (θ : ℝ) ^ 2) =
      (θ : ℝ) * (w i ^ 2 / (i : ℝ)) +
        (θ : ℝ) ^ 2 * ∑ j ∈ Icc 1 (n - 1), w i * w j * fuSigma n i j := by
    intro i hi
    simp_rw [mul_add, mul_ite, mul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hi, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [← covariance_self hmeas,
    covariance_fun_sum_fun_sum' (X := fun i x => w i * markedKingmanSfs n i x)
      (Y := fun i x => w i * markedKingmanSfs n i x) (fun i _ => hlp i) (fun i _ => hlp i),
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i hi j hj,
    Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem sum_Icc_one_cast_cube (m : ℕ) :
    ∑ i ∈ Icc 1 m, (i : ℝ) ^ 3 = ((m : ℝ) * ((m : ℝ) + 1) / 2) ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem sum_Icc_one_mul_sub_sq (m : ℕ) (N : ℝ) :
    ∑ i ∈ Icc 1 m, (i : ℝ) * (N - 2 * (i : ℝ)) ^ 2 =
      N ^ 2 * (m : ℝ) * ((m : ℝ) + 1) / 2 -
        2 * N * (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 3 +
        (m : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Source: fu1995, p. 175, eq. (1), p. 174; durrett2008, Thm 2.2; durrett2008, eq. (2.22). -/
theorem markedKingman_fayWu_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance
        (fun x => (2 / ((n : ℝ) * ((n : ℝ) - 1))) *
          ∑ i ∈ Icc 1 (n - 1), (i : ℝ) ^ 2 * markedKingmanSfs n i x) (markedKingmanLaw n θ) =
      (θ : ℝ) + (θ : ℝ) ^ 2 * ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) *
          (2 * (j : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) * fuSigma n i j := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf : (fun x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) =>
      (2 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ i ∈ Icc 1 (n - 1), (i : ℝ) ^ 2 * markedKingmanSfs n i x) =
      fun x => ∑ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) * markedKingmanSfs n i x := by
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : ∑ i ∈ Icc 1 (n - 1),
      (2 * (i : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) ^ 2 / (i : ℝ) = 1 := by
    have hterm : ∀ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) ^ 2 / (i : ℝ) =
          4 / ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * (i : ℝ) ^ 3 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      norm_num
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_Icc_one_cast_cube,
      Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
    ring
  rw [hf, markedKingman_linear_sfs_variance n
    (fun i : ℕ => 2 * (i : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) θ, hw, mul_one]

/-- Source: fu1995, pp. 175–176, eq. (1), p. 174; durrett2008, Thm 2.2. -/
theorem markedKingman_fayWuNumerator_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance
        (fun x => markedKingmanPi n x - (2 / ((n : ℝ) * ((n : ℝ) - 1))) *
          ∑ i ∈ Icc 1 (n - 1), (i : ℝ) ^ 2 * markedKingmanSfs n i x) (markedKingmanLaw n θ) =
      2 * ((n : ℝ) - 2) / (3 * ((n : ℝ) - 1)) * (θ : ℝ) +
        (θ : ℝ) ^ 2 * ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
          (2 * (i : ℝ) * ((n : ℝ) - 2 * i) / ((n : ℝ) * ((n : ℝ) - 1))) *
            (2 * (j : ℝ) * ((n : ℝ) - 2 * j) / ((n : ℝ) * ((n : ℝ) - 1))) * fuSigma n i j := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf : (fun x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) =>
      markedKingmanPi n x - (2 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ i ∈ Icc 1 (n - 1), (i : ℝ) ^ 2 * markedKingmanSfs n i x) =
      fun x => ∑ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) * ((n : ℝ) - 2 * i) / ((n : ℝ) * ((n : ℝ) - 1))) *
          markedKingmanSfs n i x := by
    funext x
    rw [markedKingmanPi_eq_sum_sfs, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hw : ∑ i ∈ Icc 1 (n - 1),
      (2 * (i : ℝ) * ((n : ℝ) - 2 * i) / ((n : ℝ) * ((n : ℝ) - 1))) ^ 2 / (i : ℝ) =
      2 * ((n : ℝ) - 2) / (3 * ((n : ℝ) - 1)) := by
    have hterm : ∀ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) * ((n : ℝ) - 2 * i) / ((n : ℝ) * ((n : ℝ) - 1))) ^ 2 / (i : ℝ) =
          4 / ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * ((i : ℝ) * ((n : ℝ) - 2 * (i : ℝ)) ^ 2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_Icc_one_mul_sub_sq,
      Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
    ring
  rw [hf, markedKingman_linear_sfs_variance n
    (fun i : ℕ => 2 * (i : ℝ) * ((n : ℝ) - 2 * i) / ((n : ℝ) * ((n : ℝ) - 1))) θ, hw]
  ring

end Rhone.Statistics
