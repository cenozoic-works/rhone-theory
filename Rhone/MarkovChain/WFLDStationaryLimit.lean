/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDHeterozygosityPositive
public import Rhone.MarkovChain.WFLDRatioPositive
public import Rhone.MarkovChain.WFLDScaledRatio

/-!
# Stationary finite-chain LD ratio and its rare-mutation large-population limit

Source: ohta_kimura1971_ld, eq. (9), p. 574. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Filter Finset
open scoped Topology

theorem ld_stationary_sigma_exact (M : ℕ) (hM : 3 ≤ M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    ldStationaryMoments M π 2 / ldStationaryMoments M π 0 =
      ldSigmaNumerator M c u / ldSigmaDenominator M c u := by
  have hM0 : 0 < M := by omega
  have hH := ld_stationary_heterozygosity_pos M (by omega) c u hc0 hc1 hu0 hu1 π hπ hnorm hstat
  have hD := ld_sigma_denominator_pos M c u (by exact_mod_cast hM) hc0 hc1 hu0.le hu1.le
  apply (div_eq_div_iff hH.ne' hD.ne').2
  have hh := ld_stationary_sigma_cross M hM0 c u hc0 hc1 hu0.le hu1.le π hstat
  nlinarith only [hh]

/-- Source: ohta_kimura1971_ld, eq. (9), p. 574. -/
theorem ld_stationary_sigma_limit (N : ℕ → ℕ) (u : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hN : ∀ n, 3 ≤ N n) (hc : ∀ n, R / (2 * (N n : ℝ)) ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → Rhone.MarkovChain.AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a * forcedCountKernel (N n) (R / (2 * (N n : ℝ))) (u n) a b = π n b)
    (hlarge : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hrare : Tendsto (fun n => u n * (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ldStationaryMoments (N n) (π n) 2 /
      ldStationaryMoments (N n) (π n) 0) atTop (𝓝 ((10+R)/(22+13*R+R^2))) := by
  have ht : Tendsto (fun n => 1/(N n : ℝ)) atTop (𝓝 0) :=
    by simpa only [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp hlarge)
  have heq (n : ℕ) : ldStationaryMoments (N n) (π n) 2 /
      ldStationaryMoments (N n) (π n) 0 =
      ldScaledNumerator (1/(N n : ℝ)) R (u n * (N n : ℝ)) /
        ldScaledDenominator (1/(N n : ℝ)) R (u n * (N n : ℝ)) := by
    have hN0 : 0 < (N n : ℝ) := by exact_mod_cast (by have := hN n; omega : 0 < N n)
    rw [ld_stationary_sigma_exact (N n) (hN n) (R / (2 * (N n : ℝ))) (u n)
      (by positivity) (hc n) (hu0 n) (hu1 n) (π n) (hπ n) (hnorm n) (hstat n)]
    have hf := ld_sigma_scaled_factors (N n : ℝ) R (u n * (N n : ℝ)) hN0.ne'
    have hu : u n * (N n : ℝ)/(N n : ℝ) = u n := mul_div_cancel_right₀ _ hN0.ne'
    rw [hu] at hf
    rw [hf.1,hf.2]
    exact mul_div_mul_left _ _ (pow_ne_zero 5 hN0.ne')
  have hz := (ld_scaled_ratio_limit R hR).comp (ht.prodMk_nhds hrare)
  exact hz.congr fun n => (heq n).symm

end Rhone.MarkovChain.WFAllocationLD
