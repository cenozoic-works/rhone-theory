/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.OhtaKimura
public import Rhone.MarkovChain.WFLDStationaryLimit
public import Mathlib.Basic.Real.Basic

/-!
# Executable Ohta-Kimura ratio equals the specification

Source: ohta_kimura1971_ld, eq. (9), p. 574. -/

@[expose] public section
namespace Rhone.Computation.OhtaKimura

theorem ldSigmaNumerator_eq (m c u : Rat) :
    ((ldSigmaNumerator m c u : Rat) : ℝ) =
      Rhone.MarkovChain.WFAllocationLD.ldSigmaNumerator (m : ℝ) (c : ℝ) (u : ℝ) := by
  simp [ldSigmaNumerator, Rhone.MarkovChain.WFAllocationLD.ldSigmaNumerator]

theorem ldSigmaDenominator_eq (m c u : Rat) :
    ((ldSigmaDenominator m c u : Rat) : ℝ) =
      Rhone.MarkovChain.WFAllocationLD.ldSigmaDenominator (m : ℝ) (c : ℝ) (u : ℝ) := by
  simp [ldSigmaDenominator, Rhone.MarkovChain.WFAllocationLD.ldSigmaDenominator]

theorem ldSigma_eq (m c u : Rat) :
    ((ldSigma m c u : Rat) : ℝ) =
      Rhone.MarkovChain.WFAllocationLD.ldSigmaNumerator (m : ℝ) (c : ℝ) (u : ℝ) /
        Rhone.MarkovChain.WFAllocationLD.ldSigmaDenominator (m : ℝ) (c : ℝ) (u : ℝ) := by
  rw [ldSigma, Rat.cast_div, ldSigmaNumerator_eq, ldSigmaDenominator_eq]

theorem ldSigma_stationary (M : ℕ) (hM : 3 ≤ M) (c u : Rat)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * Rhone.MarkovChain.WFAllocationLD.forcedCountKernel M (c : ℝ) (u : ℝ) a
        b
      = π b) :
    Rhone.MarkovChain.WFAllocationLD.ldStationaryMoments M π 2 /
        Rhone.MarkovChain.WFAllocationLD.ldStationaryMoments M π 0 =
      ((ldSigma (M : Rat) c u : Rat) : ℝ) := by
  rw [ldSigma_eq]
  have := Rhone.MarkovChain.WFAllocationLD.ld_stationary_sigma_exact M hM (c : ℝ) (u : ℝ)
    (by exact_mod_cast hc0) (by exact_mod_cast hc1) (by exact_mod_cast hu0)
    (by have h := (Rat.cast_lt (K := ℝ)).2 hu1; simpa using h) π hπ hnorm hstat
  simpa using this

theorem ldSigmaLimit_eq (R : Rat) :
    ((ldSigmaLimit R : Rat) : ℝ) = (10 + (R : ℝ)) / (22 + 13 * (R : ℝ) + (R : ℝ) ^ 2) := by
  simp [ldSigmaLimit]

theorem ldSigmaLimit_tendsto (N : ℕ → ℕ) (u : ℕ → ℝ) (R : Rat) (hR : 0 ≤ R)
    (hN : ∀ n, 3 ≤ N n) (hc : ∀ n, (R : ℝ) / (2 * (N n : ℝ)) ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → Rhone.MarkovChain.AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a * Rhone.MarkovChain.WFAllocationLD.forcedCountKernel (N n)
      ((R : ℝ) / (2 * (N n : ℝ))) (u n) a b = π n b)
    (hlarge : Filter.Tendsto (fun n => (N n : ℝ)) Filter.atTop Filter.atTop)
    (hrare : Filter.Tendsto (fun n => u n * (N n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => Rhone.MarkovChain.WFAllocationLD.ldStationaryMoments (N n) (π n) 2 /
        Rhone.MarkovChain.WFAllocationLD.ldStationaryMoments (N n) (π n) 0) Filter.atTop
      (nhds ((ldSigmaLimit R : Rat) : ℝ)) := by
  rw [ldSigmaLimit_eq]
  exact Rhone.MarkovChain.WFAllocationLD.ld_stationary_sigma_limit N u (R : ℝ)
      (by exact_mod_cast hR)
    hN hc hu0 hu1 π hπ hnorm hstat hlarge hrare

end Rhone.Computation.OhtaKimura
