/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDNormalizationComparison
public import Rhone.MarkovChain.WFLDStationaryLimit

/-! # Comparison of the stationary expected `r²` with `1/(1+R)` -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset

theorem ld_sigma_reciprocal_difference (R : ℝ) (hR : 0 ≤ R) :
    |(10+R)/(22+13*R+R^2)-1/(1+R)| = 2*(R+6)/((1+R)*(22+13*R+R^2)) := by
  have h1 : 1+R ≠ 0 := by positivity
  have h2 : 22+13*R+R^2 ≠ 0 := by positivity
  have he : (10+R)/(22+13*R+R^2)-1/(1+R) =
      -(2*(R+6)/((1+R)*(22+13*R+R^2))) := by
    field_simp [h1,h2]
    ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]

theorem ld_expected_rsq_reciprocal_error (M : ℕ) (hM : 3 ≤ M) (R u : ℝ) (hR : 0 ≤ R)
    (hc : R / (2 * (M : ℝ)) ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M (R / (2 * (M : ℝ))) u a b = π b) :
    |ldExpectedRSq M π-1/(1+R)| ≤
      (∑ a, π a*|momentStatistics (countGametes M a) 0-ldStationaryMoments M π 0|)/
        ldStationaryMoments M π 0 +
      |ldSigmaNumerator M (R / (2 * (M : ℝ))) u /
        ldSigmaDenominator M (R / (2 * (M : ℝ))) u-(10+R)/(22+13*R+R^2)| +
      2*(R+6)/((1+R)*(22+13*R+R^2)) := by
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hc0 : 0 ≤ R / (2 * (M : ℝ)) := by positivity
  have hnormbound := ld_expected_rsq_sigma_comparison M (by omega)
    (R / (2 * (M : ℝ))) u hc0 hc hu0 hu1 π hπ hnorm hstat
  have hsigma := ld_stationary_sigma_exact M hM (R / (2 * (M : ℝ))) u hc0 hc
    hu0 hu1 π hπ hnorm hstat
  have htri := abs_sub_le (ldExpectedRSq M π)
    (ldStationaryMoments M π 2/ldStationaryMoments M π 0) (1/(1+R))
  have htri' := abs_sub_le (ldStationaryMoments M π 2/ldStationaryMoments M π 0)
    ((10+R)/(22+13*R+R^2)) (1/(1+R))
  rw [ld_sigma_reciprocal_difference R hR] at htri'
  rw [hsigma] at hnormbound htri htri'
  linarith

end Rhone.MarkovChain.WFAllocationLD
