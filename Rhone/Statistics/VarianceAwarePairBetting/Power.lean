/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.Test

/-! # Multiplier 128 suffices for the fixed one-third-calibrated bet -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

theorem budget_tail_bound {T : ℝ} (hT : 128 ≤ T) :
    T / 4 / (2 * T / 9 - 3) ^ 2 ≤ (1 : ℝ) / 20 := by
  have hp : 0 < 2 * T / 9 - 3 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [sq_nonneg (T - 128)]

theorem source_power (P : Law X) (N : ℕ) (Z : X → ℝ) {δ r : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hZ : ∀ x, |Z x| ≤ 1)
    (hm : rejection P Z = δ) (hs : rejection P (fun x => Z x ^ 2) = r)
    (hbudget : 128 ≤ N * signal δ r) :
    (19 : ℝ) / 20 ≤ probability (iid P N) (Rejects (tuning δ r) Z) := by
  let f : X → ℝ := fun x => Real.log (1 + tuning δ r * Z x)
  let a : ℝ := 2 * (N * signal δ r) / 9 - 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hlam : |tuning δ r| ≤ 1 / 3 := by
    rw [abs_of_pos (tuning_bounds hδ hδr).1]
    exact (tuning_bounds hδ hδr).2
  have hmean := source_log_mean P Z hδ hδr hZ hm hs
  have hsecond := source_log_second P Z hδ hδr hZ hs
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnmean : 2 * (N * signal δ r) / 9 ≤ N * rejection P f := by
    have h := mul_le_mul_of_nonneg_left hmean hN
    dsimp [f]
    nlinarith
  have hsub : ∀ z : Fin N → X, ¬Rejects (tuning δ r) Z z →
      a ≤ |(∑ i, f (z i)) - N * rejection P f| := by
    intro z hz
    have hw : wealth (tuning δ r) Z z < 20 := lt_of_not_ge hz
    have hl := (Real.log_lt_log (wealth_pos hlam Z hZ z) hw).trans log_twenty_lt_three
    rw [log_wealth hlam Z hZ z] at hl
    have hab := neg_le_abs ((∑ i, f (z i)) - N * rejection P f)
    dsimp [a, f] at *
    linarith
  have htail := (probability_mono (iid P N) hsub).trans
    (finite_chebyshev (iid P N) (fun z => ∑ i, f (z i)) (N * rejection P f) ha)
  rw [iid_centered_sq] at htail
  have hv : N * (rejection P (fun x => f x ^ 2) - rejection P f ^ 2) ≤
      (N * signal δ r) / 4 := by
    have hh := mul_le_mul_of_nonneg_left hsecond hN
    have hp := mul_nonneg hN (sq_nonneg (rejection P f))
    dsimp [f] at *
    nlinarith
  have hb : probability (iid P N) (fun z => ¬Rejects (tuning δ r) Z z) ≤ 1 / 20 :=
    htail.trans ((div_le_div_of_nonneg_right hv (sq_nonneg a)).trans
      (budget_tail_bound hbudget))
  rw [probability_complement] at hb
  linarith

end Rhone.Statistics.VarianceAwarePairBetting
