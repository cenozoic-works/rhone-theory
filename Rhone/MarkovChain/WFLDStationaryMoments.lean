/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationary

/-!
# Exact moment equilibrium of the finite two-locus count chain

Source: ewens2004, sec. 3.1; ohta_kimura1971_ld, eq. (6)–(7), p. 574. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset
open scoped Matrix

/-- Source: ohta_kimura1969_ld, eq. (3)–(5), p. 49. -/
def ldStationaryMoments (M : ℕ) (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ a, π a*momentStatistics (countGametes M a) i

def ldForcedStationaryMoments (M : ℕ) (c u : ℝ)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ a, π a*momentStatistics (forcedGametes c u (countGametes M a)) i

theorem ld_stationary_moment_equilibrium (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    ldStationaryMoments M π = samplingMomentMatrix M *ᵥ ldForcedStationaryMoments M c u π := by
  ext i
  unfold ldStationaryMoments ldForcedStationaryMoments Matrix.mulVec dotProduct
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    ∑ b, π b*momentStatistics (countGametes M b) i =
        ∑ a, π a*(∑ b, forcedCountKernel M c u a b*momentStatistics (countGametes M b) i) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      simp_rw [← mul_assoc, ← sum_mul, hstat]
    _ = ∑ a, ∑ j, samplingMomentMatrix M i j*
        (π a*momentStatistics (forcedGametes c u (countGametes M a)) j) := by
      apply sum_congr rfl
      intro a _
      have hh := congrFun (forced_sampling_moment_recursion M hM c u hc0 hc1 hu0 hu1 a) i
      rw [hh]
      simp only [Matrix.mulVec, dotProduct, mul_sum]
      apply sum_congr rfl
      intro j _
      ring

theorem ld_stationary_forced_moments (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) :
    ldForcedStationaryMoments M c u π 1 =
      (1-c)*(1-2*u)^4*ldStationaryMoments M π 1 ∧
    ldForcedStationaryMoments M c u π 2 =
      (1-c)^2*(1-2*u)^4*ldStationaryMoments M π 2 := by
  have hh (a : Rhone.MarkovChain.AlleleCounts M 4) :=
    forced_moment_statistics c u (countGametes M a) (count_gametes_total M hM a)
  constructor
  · unfold ldForcedStationaryMoments ldStationaryMoments
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [congrFun (hh a) 1]
    norm_num
    ring
  · unfold ldForcedStationaryMoments ldStationaryMoments
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [congrFun (hh a) 2]
    norm_num
    ring

end Rhone.MarkovChain.WFAllocationLD
