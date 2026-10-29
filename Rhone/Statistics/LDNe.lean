/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationaryLimit

/-!
# Moments of sampled linkage disequilibrium and a plug-in effective size

Source: hill1981, eq. (1)–(3), pp. 210–211. -/

@[expose] public section
noncomputable section

namespace Rhone.Statistics.LDNe

open Filter Finset MarkovChain Rhone.Dynamics MarkovChain.WFAllocationLD
open scoped Topology Matrix

def sampledMoments (M S : ℕ) (π : AlleleCounts M 4 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ a, π a *
    samplingExpectation S (countGametes M a) (fun b => momentStatistics (countGametes S b) i)

theorem sampledMoments_eq (M S : ℕ) (hM : 0 < M) (hS : 0 < S) (π : AlleleCounts M 4 → ℝ) :
    sampledMoments M S π = samplingMomentMatrix S *ᵥ ldStationaryMoments M π := by
  ext i
  have hrec (a : AlleleCounts M 4) :
      samplingExpectation S (countGametes M a)
          (fun b => momentStatistics (countGametes S b) i) =
        (samplingMomentMatrix S *ᵥ momentStatistics (countGametes M a)) i := by
    have hg : ∀ j, 0 ≤ TwoLocusSelection.vector (countGametes M a) j := by
      intro j
      fin_cases j <;> change 0 ≤ (_ : ℝ) / M <;> positivity
    exact congrFun (sampling_moment_recursion S hS _ hg (count_gametes_total M hM a)) i
  unfold sampledMoments ldStationaryMoments
  simp_rw [hrec]
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => ?_
  ring

def samplingCorrection (S : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((S : ℝ) / (((S : ℝ) - 1) * ((S : ℝ) - 2) * ((S : ℝ) - 3))) •
    !![(S : ℝ) ^ 2 - 4 * S + 2, -((S : ℝ) - 1), 2;
       4, (S : ℝ) ^ 2 - S + 2, -(4 * ((S : ℝ) - 1));
       -((S : ℝ) - 2), -((S : ℝ) - 1), ((S : ℝ) - 1) * ((S : ℝ) - 2)]

theorem samplingCorrection_mul (S : ℕ) (hS : 4 ≤ S) :
    samplingCorrection S * samplingMomentMatrix S = 1 := by
  have h4 : (4 : ℝ) ≤ S := by exact_mod_cast hS
  have h0 : (S : ℝ) ≠ 0 := by linarith
  have h1 : (S : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (S : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (S : ℝ) - 3 ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [samplingCorrection, samplingMomentMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem corrected_sampledMoments (M S : ℕ) (hM : 0 < M) (hS : 4 ≤ S)
    (π : AlleleCounts M 4 → ℝ) :
    samplingCorrection S *ᵥ sampledMoments M S π = ldStationaryMoments M π := by
  rw [sampledMoments_eq M S hM (by omega) π, Matrix.mulVec_mulVec, samplingCorrection_mul S hS,
    Matrix.one_mulVec]

theorem corrected_sampled_ratio (M S : ℕ) (hM : 3 ≤ M) (hS : 4 ≤ S) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    (samplingCorrection S *ᵥ sampledMoments M S π) 2 /
        (samplingCorrection S *ᵥ sampledMoments M S π) 0 =
      ldSigmaNumerator M c u / ldSigmaDenominator M c u := by
  rw [corrected_sampledMoments M S (by omega) hS π]
  exact ld_stationary_sigma_exact M hM c u hc0 hc1 hu0 hu1 π hπ hnorm hstat

def ldScaledRecombination (σ : ℝ) : ℝ :=
  ((1 - 13 * σ) + √(1 + 14 * σ + 81 * σ ^ 2)) / (2 * σ)

theorem ldScaledRecombination_limit_value {R : ℝ} (hR : 0 ≤ R) :
    ldScaledRecombination ((10 + R) / (22 + 13 * R + R ^ 2)) = R := by
  have hQ : 0 < 22 + 13 * R + R ^ 2 := by positivity
  have hsq : 1 + 14 * ((10 + R) / (22 + 13 * R + R ^ 2)) +
      81 * ((10 + R) / (22 + 13 * R + R ^ 2)) ^ 2 =
      ((R ^ 2 + 20 * R + 108) / (22 + 13 * R + R ^ 2)) ^ 2 := by
    field_simp
    ring
  have h10 : (10 : ℝ) + R ≠ 0 := by positivity
  unfold ldScaledRecombination
  rw [hsq, Real.sqrt_sq (by positivity)]
  field_simp
  ring

def ldNe (c σ : ℝ) : ℝ := ldScaledRecombination σ / (2 * c)

theorem ldNe_limit_value {N : ℕ} {c : ℝ} (hc : 0 < c) :
    ldNe c ((10 + 2 * N * c) / (22 + 13 * (2 * N * c) + (2 * N * c) ^ 2)) = N := by
  have hR : (0 : ℝ) ≤ 2 * N * c := by positivity
  unfold ldNe
  rw [ldScaledRecombination_limit_value hR]
  field_simp

theorem tendsto_ldNe_corrected_ratio (N S : ℕ → ℕ) (u : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hN : ∀ n, 3 ≤ N n) (hS : ∀ n, 4 ≤ S n) (hc : ∀ n, R / (2 * (N n : ℝ)) ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b,
      ∑ a, π n a * forcedCountKernel (N n) (R / (2 * (N n : ℝ))) (u n) a b = π n b)
    (hlarge : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hrare : Tendsto (fun n => u n * (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ldNe (R / (2 * (N n : ℝ)))
        ((samplingCorrection (S n) *ᵥ sampledMoments (N n) (S n) (π n)) 2 /
          (samplingCorrection (S n) *ᵥ sampledMoments (N n) (S n) (π n)) 0) / (N n : ℝ))
      atTop (𝓝 1) := by
  set σ₀ : ℝ := (10 + R) / (22 + 13 * R + R ^ 2) with hσ₀
  have hσpos : 0 < σ₀ := by positivity
  have hlim := ld_stationary_sigma_limit N u R hR.le hN hc hu0 hu1 π hπ hnorm hstat hlarge hrare
  have hcont : ContinuousAt ldScaledRecombination σ₀ := by
    unfold ldScaledRecombination
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hcomp := (hcont.tendsto.comp hlim).div_const R
  rw [hσ₀, ldScaledRecombination_limit_value hR.le, div_self hR.ne'] at hcomp
  refine hcomp.congr fun n => ?_
  have hNn : (N n : ℝ) ≠ 0 := by
    have := hN n
    positivity
  rw [corrected_sampledMoments (N n) (S n) (by have := hN n; omega) (hS n) (π n)]
  simp only [Function.comp_apply, ldNe]
  field_simp

end Rhone.Statistics.LDNe
