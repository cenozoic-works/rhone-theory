/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Power

/-! # Adjustable threshold for the fixed finite-category scan -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

def RejectsAt {N : ℕ} (T : ℝ) (z : Fin N → ℝ) : Prop :=
  0 < squareStatistic z ∧ T * squareStatistic z ≤ (sumStatistic z) ^ 2

theorem good_event_rejects_at {N : ℕ} (z : Fin N → ℝ) {δ d T : ℝ} (hT : 20 ≤ T)
    (hδ : δ ≠ 0) (hN : 0 < (N : ℝ)) (_hd : 0 < d)
    (hb : 8 * T * d ≤ N * δ ^ 2)
    (hS : |sumStatistic z - N * δ| < N * |δ| / 2)
    (hD : squareStatistic z < 2 * N * d) : RejectsAt T z := by
  have ha : 0 < |δ| := abs_pos.mpr hδ
  have hs : N * |δ| / 2 < |sumStatistic z| := by
    have ht := abs_add_le (sumStatistic z) (N * δ - sumStatistic z)
    rw [add_sub_cancel, abs_mul, abs_of_pos hN, abs_sub_comm] at ht
    linarith
  have hs2 : N ^ 2 * δ ^ 2 / 4 < (sumStatistic z) ^ 2 := by
    have h := (sq_lt_sq₀ (by positivity : 0 ≤ N * |δ| / 2)
      (abs_nonneg (sumStatistic z))).mpr hs
    rw [sq_abs] at h
    nlinarith [sq_abs δ]
  constructor
  · have hn : 0 ≤ squareStatistic z := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    by_contra h
    have hz := squareStatistic_zero z (le_antisymm (le_of_not_gt h) hn)
    rw [hz, abs_zero] at hs
    have hp : 0 < N * |δ| / 2 := by positivity
    linarith
  · have hb' := mul_le_mul_of_nonneg_left hb hN.le
    have hTD := mul_lt_mul_of_pos_left hD (by linarith : 0 < T)
    nlinarith

theorem iid_binary_power_at (P : Law X) (N : ℕ) {T : ℝ} (hT : 20 ≤ T) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) (hδ : contrastMean P F G ≠ 0)
    (hbig : 8 * T * discordance P F G ≤ N * (contrastMean P F G) ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid P N)
      (fun x => RejectsAt T (fun i => F (x i) - G (x i))) := by
  let δ := contrastMean P F G
  let d := discordance P F G
  let f : X → ℝ := fun x => F x - G x
  change 8 * T * d ≤ N * δ ^ 2 at hbig
  have hd0 : 0 < d := lt_of_lt_of_le (abs_pos.mpr hδ)
    (abs_mean_le_discordance P hF hG)
  have hb : 160 * d ≤ N * δ ^ 2 := by nlinarith
  have had : |δ| ≤ d := abs_mean_le_discordance P hF hG
  have hdd : δ ^ 2 ≤ d ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg δ) hd0.le).mpr had
    simpa only [sq_abs] using h
  have hN : 0 < (N : ℝ) := by
    by_contra hn
    have hz : (N : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (by positivity)
    rw [hz, zero_mul] at hb
    linarith
  have hNd : 160 ≤ N * d := by
    have h := mul_le_mul_of_nonneg_left hdd hN.le
    nlinarith
  let S : (Fin N → X) → ℝ := fun x => sumStatistic (fun i => f (x i))
  let D : (Fin N → X) → ℝ := fun x => squareStatistic (fun i => f (x i))
  have hVS : rejection (iid P N) (fun x => (S x - N * δ) ^ 2) ≤ N * d := by
    exact iid_sum_variance_le P N f
  have hVD : rejection (iid P N) (fun x => (D x - N * d) ^ 2) ≤ N * d := by
    have h := iid_sum_variance_le P N (fun x => (f x) ^ 2)
    have he : (fun x => ((f x) ^ 2) ^ 2) = (fun x => (f x) ^ 2) :=
      funext (binary_fourth hF hG)
    rw [he] at h
    exact h
  have ht : 0 < N * |δ| / 2 := by positivity
  have hsBound : probability (iid P N) (fun x => N * |δ| / 2 ≤ |S x - N * δ|) ≤
      (1 : ℝ) / 40 := by
    apply (finite_chebyshev (iid P N) S (N * δ) ht).trans
    apply (div_le_div_of_nonneg_right hVS (sq_nonneg _)).trans
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    have h := mul_le_mul_of_nonneg_left hb hN.le
    rw [div_pow, mul_pow, sq_abs]
    nlinarith
  have hdBound : probability (iid P N) (fun x => 2 * N * d ≤ D x) ≤
      (1 : ℝ) / 160 := by
    have hsub : ∀ x, 2 * N * d ≤ D x → N * d ≤ |D x - N * d| := by
      intro x hx
      exact le_trans (by linarith) (le_abs_self _)
    apply (probability_mono (iid P N) hsub).trans
    apply (finite_chebyshev (iid P N) D (N * d) (mul_pos hN hd0)).trans
    apply (div_le_div_of_nonneg_right hVD (sq_nonneg _)).trans
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hN hd0))).mpr
    nlinarith [mul_nonneg (show 0 ≤ N * d by positivity) (show 0 ≤ N * d - 160 by linarith)]
  let A : (Fin N → X) → Prop := fun x => ¬ RejectsAt T (fun i => f (x i))
  have hbad : probability (iid P N) A ≤ (1 : ℝ) / 40 + 1 / 160 := by
    have hsub : ∀ x, A x →
        N * |δ| / 2 ≤ |S x - N * δ| ∨ 2 * N * d ≤ D x := by
      intro x hx
      by_contra h
      push Not at h
      exact hx (good_event_rejects_at _ hT hδ hN hd0 hbig h.1 h.2)
    exact (probability_mono (iid P N) hsub).trans
      ((probability_union_le (iid P N) _ _).trans (add_le_add hsBound hdBound))
  change probability (iid P N) (fun x => ¬ RejectsAt T (fun i => f (x i))) ≤ _ at hbad
  rw [probability_complement] at hbad
  change (19 : ℝ) / 20 ≤ probability (iid P N) (fun x => RejectsAt T (fun i => f (x i)))
  linarith

end Rhone.Statistics.PooledPairPowerIndex
