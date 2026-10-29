/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationaryMoments

/-!
# Exact stationary LD ratio from the finite count-chain moment equations

Source: ohta_kimura1971_ld, eq. (9), p. 574. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open scoped Matrix

def ldSigmaNumerator (m c u : ℝ) : ℝ :=
  m^3*(m^3-(m-2)^2*(m-1)*(1-c)*(1-2*u)^4)

def ldSigmaDenominator (m c u : ℝ) : ℝ :=
  let k := (1-c)*(1-2*u)^4
  let l := (1-c)^2*(1-2*u)^4
  let q := m^3-(m-2)^2*(m-1)*k
  (m-1)*(q*(m^3-(m^3-3*m^2+4*m-4)*l)-4*(m-1)^2*(m-2)^2*k*l)

theorem ld_stationary_sigma_cross (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    ldSigmaDenominator M c u * ldStationaryMoments M π 2 =
      ldSigmaNumerator M c u * ldStationaryMoments M π 0 := by
  have he := ld_stationary_moment_equilibrium M hM c u hc0 hc1 hu0 hu1 π hstat
  have hf := ld_stationary_forced_moments M hM c u π
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  have e2 := congrFun he 2
  norm_num [samplingMomentMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at e0 e1 e2
  rw [hf.1, hf.2] at e0 e1 e2
  field_simp [Nat.cast_ne_zero.mpr hM.ne'] at e0 e1 e2
  unfold ldSigmaDenominator ldSigmaNumerator
  dsimp only
  linear_combination
    (((M : ℝ)^3-((M : ℝ)-2)^2*((M : ℝ)-1)*(1-c)*(1-2*u)^4)*((M : ℝ)-1))*e2 -
    ((M : ℝ)^3-((M : ℝ)-2)^2*((M : ℝ)-1)*(1-c)*(1-2*u)^4)*e0 +
    (((M : ℝ)-1)^2*((M : ℝ)-2)*(1-c)*(1-2*u)^4)*e1

end Rhone.MarkovChain.WFAllocationLD
