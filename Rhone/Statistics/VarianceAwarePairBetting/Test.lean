/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.Moments

/-! # Fixed-N positive product test and uniform mean-zero null control -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

def wealth {N : ℕ} (lam : ℝ) (Z : X → ℝ) (z : Fin N → X) : ℝ :=
  ∏ i, (1 + lam * Z (z i))

def Rejects {N : ℕ} (lam : ℝ) (Z : X → ℝ) (z : Fin N → X) : Prop := 20 ≤ wealth lam Z z

theorem factor_pos {lam : ℝ} (hlam : |lam| ≤ 1 / 3) {z : ℝ} (hz : |z| ≤ 1) :
    0 < 1 + lam * z := by
  have h : |lam * z| ≤ 1 / 3 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg lam) hz).trans hlam
  have hh := (abs_le.mp h).1
  linarith

omit [Fintype X] in
theorem wealth_pos {N : ℕ} {lam : ℝ} (hlam : |lam| ≤ 1 / 3) (Z : X → ℝ)
    (hZ : ∀ x, |Z x| ≤ 1) (z : Fin N → X) : 0 < wealth lam Z z :=
  Finset.prod_pos fun i _ => factor_pos hlam (hZ (z i))

theorem null_product_mean (P : Law X) (N : ℕ) (lam : ℝ) (Z : X → ℝ)
    (hm : rejection P Z = 0) : rejection (iid P N) (wealth lam Z) = 1 := by
  change rejection (iid P N) (fun z => ∏ i, (1 + lam * Z (z i))) = 1
  rw [expectation_product P N (fun _ x => 1 + lam * Z x)]
  have he : rejection P (fun x => 1 + lam * Z x) = 1 := by
    simp only [rejection, mul_add, mul_one, Finset.sum_add_distrib, P.total]
    have hh : (∑ x, P.mass x * (lam * Z x)) = lam * rejection P Z := by
      simp only [rejection, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [hh, hm]
    ring
  simp_rw [he]
  simp

theorem common_size (P : Law X) (N : ℕ) {lam : ℝ} (hlam : |lam| ≤ 1 / 3) (Z : X → ℝ)
    (hZ : ∀ x, |Z x| ≤ 1) (hm : rejection P Z = 0) :
    probability (iid P N) (Rejects lam Z) ≤ (1 : ℝ) / 20 := by
  have h := finite_markov (iid P N) (wealth lam Z) (fun z => (wealth_pos hlam Z hZ z).le)
    (by norm_num : (0 : ℝ) < 20)
  rw [null_product_mean P N lam Z hm] at h
  exact h

theorem log_twenty_lt_three : Real.log 20 < 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 20)).mpr
  linarith

omit [Fintype X] in
theorem log_wealth {N : ℕ} {lam : ℝ} (hlam : |lam| ≤ 1 / 3) (Z : X → ℝ)
    (hZ : ∀ x, |Z x| ≤ 1) (z : Fin N → X) :
    Real.log (wealth lam Z z) = ∑ i, Real.log (1 + lam * Z (z i)) := by
  exact Real.log_prod (fun i _ => ne_of_gt (factor_pos hlam (hZ (z i))))

end Rhone.Statistics.VarianceAwarePairBetting
