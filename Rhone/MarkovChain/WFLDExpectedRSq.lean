/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDMarginalHeterozygosity
public import Rhone.Dynamics.LDMeasures

/-!
# Bounds and rare-mutation limits for the stationary expected `r²`

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset Filter
open scoped Topology

/-- Source: mcvean2002, eq. (1), p. 987. -/
def ldExpectedRSq (M : ℕ) (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) : ℝ :=
  ∑ a, π a*Dynamics.Gametes.rSq (countGametes M a).pA (countGametes M a).pB (countGametes M a).D

/-- Source: ewens2004, sec. 3.1. -/
theorem count_gametes_isDist (M : ℕ) (hM : 0 < M) (a : Rhone.MarkovChain.AlleleCounts M 4) :
    (countGametes M a).IsDist := by
  refine ⟨?_, ?_, ?_, ?_, count_gametes_total M hM a⟩ <;>
    unfold countGametes Dynamics.TwoLocusSelection.fromVector <;> positivity

/-- Source: ewens2004, sec. 3.1. -/
theorem count_rsq_marginal_bound (M : ℕ) (hM : 2 ≤ M) (a : Rhone.MarkovChain.AlleleCounts M 4) :
    ((M : ℝ)-1)*Dynamics.Gametes.rSq (countGametes M a).pA (countGametes M a).pB
        (countGametes M a).D ≤
      (M : ℝ)^2*ldMarginalH (countGametes M a) := by
  have hM0 : 0 < M := by omega
  let k := a.val 0+a.val 1
  have hkM : k ≤ M := by
    have hs := a.sum
    norm_num [Fin.sum_univ_four] at hs
    dsimp only [k]
    omega
  have hp : (countGametes M a).pA = (k : ℝ)/M := by
    unfold countGametes Dynamics.TwoLocusSelection.fromVector Dynamics.Gametes.pA
    dsimp only [k]
    norm_num
    rw [add_div]
  by_cases hk0 : k=0
  · simp [Dynamics.Gametes.rSq, ldMarginalH, hp, hk0]
  by_cases hk1 : k=M
  · simp [Dynamics.Gametes.rSq, ldMarginalH, hp, hk1, Nat.cast_ne_zero.mpr hM0.ne']
  have hleft : 0 ≤ (k : ℝ)-1 := by
    have hh : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hright : 0 ≤ (M : ℝ)-(k : ℝ)-1 := by
    have hh : (k : ℝ)+1 ≤ M := by exact_mod_cast (by omega : k+1 ≤ M)
    linarith
  have hh : (M : ℝ)-1 ≤ (M : ℝ)^2*ldMarginalH (countGametes M a) := by
    unfold ldMarginalH
    rw [hp]
    field_simp [Nat.cast_ne_zero.mpr hM0.ne']
    nlinarith [mul_nonneg hleft hright]
  have hr := Dynamics.Gametes.rSq_le_one (count_gametes_isDist M hM0 a)
  have hm1 : 0 ≤ (M : ℝ)-1 := by
    have hh : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    linarith
  exact (mul_le_mul_of_nonneg_left hr hm1).trans (by simpa only [mul_one] using hh)

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_stationary_expected_rsq_bound (M : ℕ) (hM : 2 ≤ M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    0 ≤ ldExpectedRSq M π ∧ ldExpectedRSq M π ≤ (M : ℝ)^2*u := by
  have hM0 : 0 < M := by omega
  constructor
  · exact sum_nonneg fun a _ =>
      mul_nonneg (hπ a) (Dynamics.Gametes.rSq_nonneg (count_gametes_isDist M hM0 a))
  · have hmarg := ld_stationary_marginal_heterozygosity_bound M hM0 c u
      hc0 hc1 hu0.le hu1.le π hπ hnorm hstat
    have he : ((M : ℝ)-1)*ldExpectedRSq M π ≤
        (M : ℝ)^2*(∑ a, π a*ldMarginalH (countGametes M a)) := by
      unfold ldExpectedRSq
      rw [mul_sum,mul_sum]
      apply sum_le_sum
      intro a _
      have hh := mul_le_mul_of_nonneg_left (count_rsq_marginal_bound M hM a) (hπ a)
      nlinarith only [hh]
    have hf := mul_le_mul_of_nonneg_left hmarg (sq_nonneg (M : ℝ))
    have hm1 : 0 < (M : ℝ)-1 := by
      have hh : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
      linarith
    nlinarith only [he,hf,hm1]

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_stationary_expected_rsq_rare_limit (M : ℕ) (hM : 2 ≤ M) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (u : ℕ → ℝ)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : ℕ → Rhone.MarkovChain.AlleleCounts M 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a * forcedCountKernel M c (u n) a b = π n b)
    (hrare : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ldExpectedRSq M (π n)) atTop (𝓝 0) := by
  have hh (n : ℕ) := ld_stationary_expected_rsq_bound M hM c (u n)
    hc0 hc1 (hu0 n) (hu1 n) (π n) (hπ n) (hnorm n) (hstat n)
  apply squeeze_zero (fun n => (hh n).1) (fun n => (hh n).2)
  simpa only [mul_zero] using hrare.const_mul ((M : ℝ)^2)

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_stationary_expected_rsq_variable_rare_limit (N : ℕ → ℕ) (c u : ℕ → ℝ)
    (hN : ∀ n, 2 ≤ N n) (hc0 : ∀ n, 0 ≤ c n) (hc1 : ∀ n, c n ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → Rhone.MarkovChain.AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a * forcedCountKernel (N n) (c n) (u n) a b = π n b)
    (hrare : Tendsto (fun n => (N n : ℝ) ^ 2 * u n) atTop (𝓝 0)) :
    Tendsto (fun n => ldExpectedRSq (N n) (π n)) atTop (𝓝 0) := by
  have hh (n : ℕ) := ld_stationary_expected_rsq_bound (N n) (hN n) (c n) (u n)
    (hc0 n) (hc1 n) (hu0 n) (hu1 n) (π n) (hπ n) (hnorm n) (hstat n)
  exact squeeze_zero (fun n => (hh n).1) (fun n => (hh n).2) hrare

end Rhone.MarkovChain.WFAllocationLD
