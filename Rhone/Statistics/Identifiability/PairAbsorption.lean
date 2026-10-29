/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Absorption

/-! # The remaining two-lineage island chain coalesces with probability one -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Filter
namespace Rhone.Statistics.Identifiability

noncomputable def pairLyapunov (k : Nat) (c q : ℝ) : Fin 2 → ℝ :=
  ![1 + (k + 2) / c, 1 + (k + 2) / c + 1 / (2*q)]

theorem pairLyapunov_ge_one (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ j, 1 ≤ pairLyapunov k c q j := by
  intro j
  fin_cases j
  · change 1 ≤ 1 + (k + 2 : ℝ) / c
    have h : 0 ≤ (k + 2 : ℝ) / c := by positivity
    linarith
  · change 1 ≤ 1 + (k + 2 : ℝ) / c + 1 / (2*q)
    have h : 0 ≤ (k + 2 : ℝ) / c := by positivity
    have h' : 0 ≤ 1 / (2*q) := by positivity
    linarith

theorem pairLyapunov_drift (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    MarkovChain.Identifiability.pairGenerator k c q *ᵥ pairLyapunov k c q = ![-c-1, -1] := by
  ext j
  fin_cases j <;>
    simp [MarkovChain.Identifiability.pairGenerator, pairLyapunov,
        MarkovChain.Identifiability.totalMigration, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> field_simp [hc, hq] <;> ring

theorem pair_survival_tendsto_zero (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (i : Fin 2) :
    Tendsto (flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
        MarkovChain.Identifiability.pairSurvival 0) atTop (𝓝 0) := by
  apply survival_tendsto_zero_of_lyapunov _ (pairGenerator_metzler k hq.le)
    (pairLyapunov k c q) (pairLyapunov_ge_one k hc hq) zero_lt_one
  intro j
  rw [pairLyapunov_drift k hc.ne' hq.ne']
  fin_cases j
  · change -c - 1 ≤ -(1 : ℝ)
    linarith
  · exact le_refl _

theorem pair_exitRate (k : Nat) (c q : ℝ) : exitRate
    (MarkovChain.Identifiability.pairGenerator k c q) = MarkovChain.Identifiability.pairDensity c :=
    by
  ext i
  fin_cases i <;> simp
      [exitRate, MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.pairDensity,
      Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

end Rhone.Statistics.Identifiability
