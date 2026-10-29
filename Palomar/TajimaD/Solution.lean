module

public import Rhone.Statistics.SfsMarkedSpectrum
public import Rhone.Statistics.TajimaD

@[expose] public section

namespace Rhone.Palomar.TajimaD

open Coalescent Probability Statistics MeasureTheory ProbabilityTheory
open scoped NNReal

theorem markedKingmanLaw_probability (n : ℕ) (θ : ℝ≥0) :
    IsProbabilityMeasure (markedKingmanLaw n θ) :=
  Rhone.Coalescent.markedKingmanLaw_probability n θ

theorem markedKingmanTajimaVarianceEstimate_eq (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanTajimaVarianceEstimate n x =
      tajimaVarianceEstimate n (markedKingmanSegregating n x) :=
  Rhone.Statistics.markedKingmanTajimaVarianceEstimate_eq n x

theorem markedKingmanTajimaD_eq (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanTajimaD n x = markedKingmanTajimaNumerator n x /
      Real.sqrt (markedKingmanTajimaVarianceEstimate n x) :=
  Rhone.Statistics.markedKingmanTajimaD_eq n x

theorem tajimaD_of_varianceEstimate_nonpos (n : ℕ) (π S : ℝ)
    (h : tajimaVarianceEstimate n S ≤ 0) : tajimaD n π S = 0 :=
  Rhone.Statistics.tajimaD_of_varianceEstimate_nonpos n π S h

theorem tajimaD_zero_segregating (n : ℕ) (π : ℝ) : tajimaD n π 0 = 0 :=
  Rhone.Statistics.tajimaD_zero_segregating n π

theorem tajimaD_two (π S : ℝ) : tajimaD 2 π S = 0 :=
  Rhone.Statistics.tajimaD_two π S

theorem tajimaD_three (π S : ℝ) : tajimaD 3 π S = 0 :=
  Rhone.Statistics.tajimaD_three π S

theorem measurable_markedKingmanTajimaD (n : ℕ) : Measurable (markedKingmanTajimaD n) :=
  Rhone.Statistics.measurable_markedKingmanTajimaD n

theorem markedKingmanTajimaNumerator_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaNumerator n x ∂markedKingmanLaw n θ = 0 :=
  Rhone.Statistics.markedKingmanTajimaNumerator_mean hn θ

theorem markedKingmanPi_mul_segregating_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x * markedKingmanSegregating n x ∂markedKingmanLaw n θ =
      (θ : ℝ) + ((tajimaA1 n : ℝ) + ((n : ℝ) + 2) / (2 * n)) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanPi_mul_segregating_mean hn θ

theorem markedKingmanPi_segregating_covariance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanPi n x - θ) *
        (markedKingmanSegregating n x - (θ : ℝ) * (tajimaA1 n : ℝ)) ∂markedKingmanLaw n θ =
      (θ : ℝ) + ((n : ℝ) + 2) / (2 * n) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanPi_segregating_covariance hn θ

theorem markedKingmanTajimaNumerator_second_moment {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaNumerator n x ^ 2 ∂markedKingmanLaw n θ =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanTajimaNumerator_second_moment hn θ

theorem markedKingmanTajimaNumerator_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanTajimaNumerator n) (markedKingmanLaw n θ) =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanTajimaNumerator_variance hn θ

theorem markedKingmanTajimaVarianceEstimate_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaVarianceEstimate n x ∂markedKingmanLaw n θ =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanTajimaVarianceEstimate_mean hn θ

theorem markedKingmanTajimaVarianceEstimate_unbiased {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaVarianceEstimate n x ∂markedKingmanLaw n θ =
      ProbabilityTheory.variance (markedKingmanTajimaNumerator n) (markedKingmanLaw n θ) :=
  Rhone.Statistics.markedKingmanTajimaVarianceEstimate_unbiased hn θ

theorem markedKingmanSfs_mean {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ = (θ : ℝ) / i :=
  Rhone.Statistics.markedKingmanSfs_mean hi hin θ

theorem sum_markedKingmanSfs_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∑ i ∈ Finset.Icc 1 (n - 1), ∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ =
      ∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ :=
  Rhone.Statistics.sum_markedKingmanSfs_mean hn θ

theorem expSfs_eq (θ : ℚ) {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    expSfs θ n i = θ / i :=
  Rhone.Statistics.expSfs_eq θ hi hin

theorem expSfs_eq_integral_markedKingmanSfs (θ : ℚ) (hθ : 0 ≤ θ) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) :
    ((expSfs θ n i : ℚ) : ℝ) =
      ∫ x, markedKingmanSfs n i x
        ∂markedKingmanLaw n (NNReal.mk (θ : ℝ) (by exact_mod_cast hθ)) :=
  Rhone.Statistics.expSfs_eq_integral_markedKingmanSfs θ hθ hi hin

end Rhone.Palomar.TajimaD
