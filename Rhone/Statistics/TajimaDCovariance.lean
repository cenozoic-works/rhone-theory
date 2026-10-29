/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.TajimaDNumerator
public import Rhone.Statistics.TajimaDCrossMoment

/-!
# Covariance of pairwise diversity and segregating sites, and the variance of `π - S / a1`

Source: tajima1989, p. 587, eq. (24), p. 588, eq. (30); watterson1975, p. 258, eq. (1.5a);
fu_li1993, p. 696, eq. (20)–(21). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter
open scoped NNReal

private theorem pi_poisson_integral_weighted_count_mul {ι : Type*} [Fintype ι]
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

theorem integral_kingmanBranchMutationKernel_pi_mul_segregating {n : ℕ} (hn : 2 ≤ n)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanPi n (h, x) * markedKingmanSegregating n (h, x)
      ∂kingmanBranchMutationKernel n θ h =
    ((θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h) *
        ((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) +
      (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h := by
  change (∫ x, (∑ b : KingmanMutationBranch n, kingmanBranchPairWeight n b.2 * (x b : ℝ)) *
      (∑ b : KingmanMutationBranch n, (x b : ℝ))
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  have hm := pi_poisson_integral_weighted_count_mul (kingmanBranchMutationRate n θ h)
    (fun b => kingmanBranchPairWeight n b.2) (fun _ => (1 : ℝ))
  simp only [one_mul, mul_one] at hm
  rw [hm, sum_kingmanBranchMutationRate_weight hn, sum_kingmanBranchMutationRate]

theorem integrable_markedKingmanPi_mul_segregating {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanPi n x * markedKingmanSegregating n x)
      (markedKingmanLaw n θ) := by
  have hp : MemLp (markedKingmanPi n) 2 (markedKingmanLaw n θ) :=
    (memLp_two_iff_integrable_sq (measurable_markedKingmanPi n).aestronglyMeasurable).2
      (integrable_markedKingmanPi_sq hn θ)
  have hs : MemLp (markedKingmanSegregating n) 2 (markedKingmanLaw n θ) :=
    (memLp_two_iff_integrable_sq (measurable_markedKingmanSegregating n).aestronglyMeasurable).2
      (integrable_markedKingmanSegregating_sq n θ)
  exact hp.integrable_mul hs

theorem markedKingmanPi_mul_segregating_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x * markedKingmanSegregating n x ∂markedKingmanLaw n θ =
      (θ : ℝ) + ((tajimaA1 n : ℝ) + ((n : ℝ) + 2) / (2 * n)) * (θ : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanPi_mul_segregating hn θ)]
  simp_rw [integral_kingmanBranchMutationKernel_pi_mul_segregating hn]
  have he : (fun h : KingmanMutationHistory n =>
      ((θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h) *
          ((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) +
        (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h) =
      fun h => ((θ : ℝ) / 2) ^ 2 * (kingmanFiniteReward n (kingmanDiversityReward n) h *
          kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) +
        (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h := by
    funext h
    ring
  rw [he, integral_add ((integrable_kingmanFiniteDiversityReward_mul_length hn).const_mul _)
      ((integrable_kingmanFiniteDiversityReward hn).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_kingmanFiniteDiversityReward_mul_length hn,
    integral_kingmanFiniteDiversityReward hn, kingmanDiversityReward_bot hn]
  field_simp
  ring

/-- Source: tajima1989, p. 587, eq. (24). -/
theorem markedKingmanPi_segregating_covariance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanPi n x - θ) *
        (markedKingmanSegregating n x - (θ : ℝ) * (tajimaA1 n : ℝ)) ∂markedKingmanLaw n θ =
      (θ : ℝ) + ((n : ℝ) + 2) / (2 * n) * (θ : ℝ) ^ 2 := by
  have ips := integrable_markedKingmanPi_mul_segregating hn θ
  have ip : Integrable (fun x => ((θ : ℝ) * (tajimaA1 n : ℝ)) * markedKingmanPi n x)
      (markedKingmanLaw n θ) := (integrable_markedKingmanPi hn θ).const_mul _
  have isg : Integrable (fun x => (θ : ℝ) * markedKingmanSegregating n x)
      (markedKingmanLaw n θ) := (integrable_markedKingmanSegregating n θ).const_mul _
  have i1 : Integrable (fun x => markedKingmanPi n x * markedKingmanSegregating n x -
      ((θ : ℝ) * (tajimaA1 n : ℝ)) * markedKingmanPi n x) (markedKingmanLaw n θ) :=
    ips.sub ip
  have i2 : Integrable (fun x => (markedKingmanPi n x * markedKingmanSegregating n x -
      ((θ : ℝ) * (tajimaA1 n : ℝ)) * markedKingmanPi n x) -
      (θ : ℝ) * markedKingmanSegregating n x) (markedKingmanLaw n θ) := i1.sub isg
  have he : (fun x => (markedKingmanPi n x - θ) *
      (markedKingmanSegregating n x - (θ : ℝ) * (tajimaA1 n : ℝ))) =
      fun x => ((markedKingmanPi n x * markedKingmanSegregating n x -
        ((θ : ℝ) * (tajimaA1 n : ℝ)) * markedKingmanPi n x) -
        (θ : ℝ) * markedKingmanSegregating n x) + (θ : ℝ) * ((θ : ℝ) * (tajimaA1 n : ℝ)) := by
    funext x
    ring
  rw [he, integral_add i2 (integrable_const _), integral_sub i1 isg, integral_sub ips ip,
    integral_const_mul, integral_const_mul, markedKingmanPi_mul_segregating_mean hn θ,
    markedKingmanPi_mean hn θ, markedKingmanSegregating_mean hn θ]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    one_mul]
  ring

private theorem numerator_sq_eq (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanTajimaNumerator n x ^ 2 =
      (markedKingmanPi n x ^ 2 - (2 / (tajimaA1 n : ℝ)) *
        (markedKingmanPi n x * markedKingmanSegregating n x)) +
      (1 / (tajimaA1 n : ℝ) ^ 2) * markedKingmanSegregating n x ^ 2 := by
  unfold markedKingmanTajimaNumerator markedKingmanWatterson
  ring

theorem integrable_markedKingmanTajimaNumerator_sq {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanTajimaNumerator n x ^ 2) (markedKingmanLaw n θ) := by
  simp_rw [numerator_sq_eq]
  exact ((integrable_markedKingmanPi_sq hn θ).sub
    ((integrable_markedKingmanPi_mul_segregating hn θ).const_mul _)).add
    ((integrable_markedKingmanSegregating_sq n θ).const_mul _)

theorem markedKingmanTajimaNumerator_second_moment {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaNumerator n x ^ 2 ∂markedKingmanLaw n θ =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha1 : (tajimaA1 n : ℝ) ≠ 0 := (tajimaA1_real_pos hn).ne'
  have hc1 : (tajimaC1 n : ℝ) = (tajimaB1 n : ℝ) - 1 / (tajimaA1 n : ℝ) := by
    rw [tajimaC1, Rat.cast_sub, Rat.cast_div, Rat.cast_one]
  have hc2 : (tajimaC2 n : ℝ) = (tajimaB2 n : ℝ) -
      ((n : ℝ) + 2) / ((tajimaA1 n : ℝ) * n) + (tajimaA2 n : ℝ) / (tajimaA1 n : ℝ) ^ 2 := by
    rw [tajimaC2]
    push_cast
    ring
  have ips : Integrable (fun x => (2 / (tajimaA1 n : ℝ)) *
      (markedKingmanPi n x * markedKingmanSegregating n x)) (markedKingmanLaw n θ) :=
    (integrable_markedKingmanPi_mul_segregating hn θ).const_mul _
  have iss : Integrable (fun x => (1 / (tajimaA1 n : ℝ) ^ 2) *
      markedKingmanSegregating n x ^ 2) (markedKingmanLaw n θ) :=
    (integrable_markedKingmanSegregating_sq n θ).const_mul _
  have i1 : Integrable (fun x => markedKingmanPi n x ^ 2 - (2 / (tajimaA1 n : ℝ)) *
      (markedKingmanPi n x * markedKingmanSegregating n x)) (markedKingmanLaw n θ) :=
    (integrable_markedKingmanPi_sq hn θ).sub ips
  simp_rw [numerator_sq_eq]
  rw [integral_add i1 iss, integral_sub (integrable_markedKingmanPi_sq hn θ) ips,
    integral_const_mul, integral_const_mul, markedKingmanPi_second_moment hn θ,
    markedKingmanPi_mul_segregating_mean hn θ, markedKingmanSegregating_second_moment hn θ,
    hc1, hc2]
  field_simp
  ring

/-- Source: tajima1989, p. 588, eq. (29)–(30). -/
theorem markedKingmanTajimaNumerator_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanTajimaNumerator n) (markedKingmanLaw n θ) =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 := by
  have hlp : MemLp (markedKingmanTajimaNumerator n) 2 (markedKingmanLaw n θ) :=
    (memLp_two_iff_integrable_sq
      (measurable_markedKingmanTajimaNumerator n).aestronglyMeasurable).2
      (integrable_markedKingmanTajimaNumerator_sq hn θ)
  rw [variance_eq_sub hlp]
  change (∫ x, markedKingmanTajimaNumerator n x ^ 2 ∂markedKingmanLaw n θ) -
    (∫ x, markedKingmanTajimaNumerator n x ∂markedKingmanLaw n θ) ^ 2 = _
  rw [markedKingmanTajimaNumerator_second_moment hn θ, markedKingmanTajimaNumerator_mean hn θ]
  ring

/-- Source: tajima1989, p. 588, eq. (34)–(35). -/
theorem markedKingmanTajimaVarianceEstimate_unbiased {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaVarianceEstimate n x ∂markedKingmanLaw n θ =
      ProbabilityTheory.variance (markedKingmanTajimaNumerator n) (markedKingmanLaw n θ) := by
  rw [markedKingmanTajimaVarianceEstimate_mean hn θ, markedKingmanTajimaNumerator_variance hn θ]

end Rhone.Statistics
