/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Statistic
public import Rhone.Statistics.DependentPairedTest.Features

/-! # Power guarantee of the fixed rejection rule for iid binary contrasts -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

theorem squareStatistic_zero {N : ℕ} (z : Fin N → ℝ)
    (h : squareStatistic z = 0) : sumStatistic z = 0 := by
  have hz : ∀ i, z i = 0 := by
    intro i
    have hi : (z i) ^ 2 ≤ squareStatistic z :=
      Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
    rw [h] at hi
    nlinarith [sq_nonneg (z i)]
  simp [sumStatistic, hz]

theorem good_event_rejects {N : ℕ} (z : Fin N → ℝ) {δ d : ℝ}
    (hδ : δ ≠ 0) (hN : 0 < (N : ℝ)) (_hd : 0 < d)
    (hb : 160 * d ≤ N * δ ^ 2)
    (hS : |sumStatistic z - N * δ| < N * |δ| / 2)
    (hD : squareStatistic z < 2 * N * d) : Rejects z := by
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
    nlinarith

theorem iid_sum_variance_le (P : Law X) (N : ℕ) (f : X → ℝ) :
    rejection (iid P N) (fun x => ((∑ i, f (x i)) - N * rejection P f) ^ 2) ≤
      N * rejection P (fun x => (f x) ^ 2) := by
  rw [iid_centered_sq]
  have := sq_nonneg (rejection P f)
  nlinarith [show (0 : ℝ) ≤ N by positivity]

omit [Fintype X] in
theorem binary_fourth {F G : X → ℝ} (hF : Binary F) (hG : Binary G) (x : X) :
    ((F x - G x) ^ 2) ^ 2 = (F x - G x) ^ 2 := by
  rcases hF x with hf | hf <;> rcases hG x with hg | hg <;> norm_num [hf, hg]

theorem iid_binary_power (P : Law X) (N : ℕ) {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) (hδ : contrastMean P F G ≠ 0)
    (hb : 160 * discordance P F G ≤ N * (contrastMean P F G) ^ 2) :
    (19 : ℝ) / 20 ≤ probability (iid P N)
      (fun x => Rejects (fun i => F (x i) - G (x i))) := by
  let δ := contrastMean P F G
  let d := discordance P F G
  let f : X → ℝ := fun x => F x - G x
  change 160 * d ≤ N * δ ^ 2 at hb
  have hd0 : 0 < d := lt_of_lt_of_le (abs_pos.mpr hδ)
    (abs_mean_le_discordance P hF hG)
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
  let A : (Fin N → X) → Prop := fun x => ¬ Rejects (fun i => f (x i))
  have hbad : probability (iid P N) A ≤ (1 : ℝ) / 40 + 1 / 160 := by
    have hsub : ∀ x, A x →
        N * |δ| / 2 ≤ |S x - N * δ| ∨ 2 * N * d ≤ D x := by
      intro x hx
      by_contra h
      push Not at h
      exact hx (good_event_rejects _ hδ hN hd0 hb h.1 h.2)
    exact (probability_mono (iid P N) hsub).trans
      ((probability_union_le (iid P N) _ _).trans (add_le_add hsBound hdBound))
  change probability (iid P N) (fun x => ¬ Rejects (fun i => f (x i))) ≤ _ at hbad
  rw [probability_complement] at hbad
  change (19 : ℝ) / 20 ≤ probability (iid P N) (fun x => Rejects (fun i => f (x i)))
  linarith

end Rhone.Statistics.DependentPairedTest
