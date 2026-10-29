/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.SimpleFiber
public import Rhone.Probability.DiagonalChain.Cleared

/-! # Survival of the marked diagonal factor in the cleared chain -/

@[expose] public section

namespace Rhone.Probability.DiagonalObstruction

open Finset LinearAlgebra.Tridiag Analysis.RecombinationExpansion
  LinearAlgebra.RecombinationExpansion DiagonalChain Analysis.RareAlleleHierarchy
  RareAlleleHierarchy

theorem dcoef_marked_eq {m k t : ℕ} (hk : 1 ≤ k) (ht : t ≤ k) :
    dcoef ℚ k k (Algebra.DiagonalObstruction.markedPoint m) 0 0 t =
      4 * (k : ℚ) * ((k : ℚ) - m) - (t : ℚ) * (4 * (k : ℚ) - t - 1) := by
  have ht' : t ≤ k + k := by omega
  have hk' : 1 ≤ k + k - t := by omega
  simp only [dcoef, Algebra.DiagonalObstruction.markedPoint, zero_mul, add_zero, Nat.cast_mul,
    Nat.cast_sub ht', Nat.cast_sub hk', Nat.cast_add, Nat.cast_one]
  ring

theorem dcoef_marked_nonpos {m k t : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (ht : t ≤ k) :
    dcoef ℚ k k (Algebra.DiagonalObstruction.markedPoint m) 0 0 t ≤ 0 := by
  rw [dcoef_marked_eq hk ht]
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hkmq : (k : ℚ) ≤ m := by exact_mod_cast hkm
  have htq : (t : ℚ) ≤ k := by exact_mod_cast ht
  have ht0 : (0 : ℚ) ≤ t := by positivity
  have hfirst : 4 * (k : ℚ) * ((k : ℚ) - m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hkmq)
  have hsecond : 0 ≤ (t : ℚ) * (4 * (k : ℚ) - t - 1) :=
    mul_nonneg ht0 (by linarith)
  linarith

theorem dcoef_marked_neg {m k t : ℕ} (hk : 1 ≤ k) (hkm : k < m) (ht : t ≤ k) :
    dcoef ℚ k k (Algebra.DiagonalObstruction.markedPoint m) 0 0 t < 0 := by
  rw [dcoef_marked_eq hk ht]
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hkmq : (k : ℚ) < m := by exact_mod_cast hkm
  have htq : (t : ℚ) ≤ k := by exact_mod_cast ht
  have ht0 : (0 : ℚ) ≤ t := by positivity
  have hfirst : 4 * (k : ℚ) * ((k : ℚ) - m) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hkmq)
  have hsecond : 0 ≤ (t : ℚ) * (4 * (k : ℚ) - t - 1) :=
    mul_nonneg ht0 (by linarith)
  linarith

theorem ED_marked_ne_zero {m k : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    ED k (Algebra.DiagonalObstruction.markedPoint m) 0 ≠ 0 := by
  rw [ED, E_rho_zero, Nat.min_self]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  exact (dcoef_marked_neg hk hkm (by have := t.isLt; omega)).ne

theorem frakE_marked_pred_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    frakE (m - 1) (Algebra.DiagonalObstruction.markedPoint m) 0 ≠ 0 := by
  rw [frakE]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  exact ED_marked_ne_zero (by omega) (by omega)

private theorem signed_cont_zero (k t : ℕ) (θ : ℚ) :
    (-1 : ℚ) ^ t * cont (dcoef ℚ k k θ 0 0) (bcoef ℚ k k) (ccoef ℚ 0) t =
      ∏ u ∈ Finset.range t, -dcoef ℚ k k θ 0 0 u := by
  rw [cont_rho_zero, Finset.prod_neg, Finset.card_range]

private theorem signed_Qc_zero (k s : ℕ) (θ : ℚ) (hs : s ≤ k + 1) :
    (-1 : ℚ) ^ (k + 1 - s) *
        Qc (dcoef ℚ k k θ 0 0) (bcoef ℚ k k) (ccoef ℚ 0) (k + 1) s =
      ∏ u ∈ Finset.range (k + 1 - s), -dcoef ℚ k k θ 0 0 (u + s) := by
  rw [Qc_of_le _ _ _ hs, tridFrom_eq_trid_shift, det_trid_eq_cont,
    cont_of_offdiag_zero _ _ _ (fun u => by simp [ccoef]),
    Finset.prod_neg, Finset.card_range]

private theorem adj_sign_factor {k t u : ℕ} (hu : u ≤ k) :
    (-1 : ℚ) ^ (k + t + u) = (-1 : ℚ) ^ t * (-1 : ℚ) ^ (k - u) := by
  calc
    (-1 : ℚ) ^ (k + t + u) =
        (-1 : ℚ) ^ t * (-1 : ℚ) ^ (k - u) * ((-1 : ℚ) ^ (2 * u)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ = _ := by norm_num [pow_mul]

private theorem upper_product_pos {k t u : ℕ} (hu : u ≤ k) :
    (0 : ℚ) < 2 ^ (u - t) *
      ∏ s ∈ Finset.Ico t u, (((k - s) * (k - s) : ℕ) : ℚ) := by
  apply mul_pos (pow_pos (by norm_num) _)
  apply Finset.prod_pos
  intro s hs
  have hs' := Finset.mem_Ico.mp hs
  have hk : 0 < (k - s) * (k - s) := Nat.mul_pos (by omega) (by omega)
  exact_mod_cast hk

theorem signed_adjD_marked_nonneg {m k t u : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (_ht : t ≤ k) (hu : u ≤ k) :
    0 ≤ (-1 : ℚ) ^ (k + t + u) * adjD k (Algebra.DiagonalObstruction.markedPoint m) 0 t u := by
  by_cases htu : t ≤ u
  · have hc : 0 ≤ (-1 : ℚ) ^ t *
        cont (dcoef ℚ k k (Algebra.DiagonalObstruction.markedPoint m) 0 0) (bcoef ℚ k k) (ccoef ℚ 0)
            t := by
      rw [signed_cont_zero]
      apply Finset.prod_nonneg
      intro s hs
      exact neg_nonneg.mpr (dcoef_marked_nonpos hk hkm (by
        have hs' := Finset.mem_range.mp hs
        omega))
    have hq : 0 ≤ (-1 : ℚ) ^ (k - u) *
        Qc (dcoef ℚ k k (Algebra.DiagonalObstruction.markedPoint m) 0 0) (bcoef ℚ k k) (ccoef ℚ 0)
          (k + 1) (u + 1) := by
      rw [show k - u = k + 1 - (u + 1) by omega, signed_Qc_zero k (u + 1) _ (by omega)]
      apply Finset.prod_nonneg
      intro s hs
      exact neg_nonneg.mpr (dcoef_marked_nonpos hk hkm (by
        have hs' := Finset.mem_range.mp hs
        omega))
    rw [adjD, usmaniEntry_T_of_le k k _ 0 0 htu, Nat.min_self, adj_sign_factor hu]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_nonneg (le_of_lt (upper_product_pos (t := t) hu)) (mul_nonneg hc hq)
  · rw [adjD, usmaniEntry_T_of_ge k k _ 0 0 (by omega : u ≤ t)]
    simp [zero_pow (by omega : t - u ≠ 0)]

theorem signed_adjD_zero_top_pos (k : ℕ) (θ : ℚ) :
    0 < (-1 : ℚ) ^ (k + 0 + k) * adjD k θ 0 0 k := by
  rw [adj_sign_factor (le_refl k), Nat.sub_self]
  simp only [pow_zero, one_mul]
  rw [adjD, usmaniEntry_T_of_le k k θ 0 0 (Nat.zero_le k), Nat.min_self]
  simp only [Nat.sub_zero, cont, Qc_self, mul_one]
  exact upper_product_pos (t := 0) (le_refl k)

theorem signed_adjD_top_top_pos {m k : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    0 < (-1 : ℚ) ^ (k + k + k) * adjD k (Algebra.DiagonalObstruction.markedPoint m) 0 k k := by
  rw [adj_sign_factor (le_refl k), Nat.sub_self, pow_zero, mul_one]
  rw [adjD, usmaniEntry_T_of_le k k (Algebra.DiagonalObstruction.markedPoint m) 0 0 (le_refl k),
      Nat.min_self]
  simp only [Nat.sub_self, pow_zero, Finset.Ico_self, Finset.prod_empty,
    one_mul, Qc_self, mul_one]
  rw [signed_cont_zero]
  apply Finset.prod_pos
  intro s hs
  exact neg_pos.mpr (dcoef_marked_neg hk hkm (by
    have hs' := Finset.mem_range.mp hs
    omega))

private def stageSign : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | k + 2 => (-1) ^ (k + 3) * stageSign (k + 1)

private theorem stageSign_step {k : ℕ} (hk : 2 ≤ k) :
    stageSign k = (-1 : ℚ) ^ (k + 1) * stageSign (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rfl

private noncomputable def signedChain (m k t : ℕ) : ℚ :=
  stageSign k * (-1) ^ (t + 1) * clearedChain (Algebra.DiagonalObstruction.markedPoint m) 0 k t

private theorem signedChain_step (m : ℕ) {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    signedChain m k t = ∑ u ∈ Finset.range (k + 1),
      ((-1 : ℚ) ^ (k + t + u) * adjD k (Algebra.DiagonalObstruction.markedPoint m) 0 t u) *
        ((u * (u - 1) : ℕ) : ℚ) * signedChain m (k - 1) (u - 1) := by
  rw [signedChain, clearedChain_step (Algebra.DiagonalObstruction.markedPoint m) 0 hk,
      clearedStep_eq_range,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u = 0
  · subst hu
    simp [diagSource]
  · simp only [diagSource, signedChain, stageSign_step hk]
    rw [show u - 1 + 1 = u by omega]
    have hsign : (-1 : ℚ) ^ (k + 1) * (-1 : ℚ) ^ (t + 1) =
        (-1 : ℚ) ^ (k + t + u) * (-1 : ℚ) ^ u := by
      rw [← pow_add, ← pow_add,
        show k + 1 + (t + 1) = (k + t) + 2 by omega,
        show k + t + u + u = (k + t) + 2 * u by omega]
      norm_num [pow_add, pow_mul]
    linear_combination stageSign (k - 1) * adjD k (Algebra.DiagonalObstruction.markedPoint m) 0 t
        u *
      ((u * (u - 1) : ℕ) : ℚ) * clearedChain (Algebra.DiagonalObstruction.markedPoint m) 0 (k - 1)
          (u - 1) * hsign

private theorem signed_term_nonneg {m k t u : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (ht : t ≤ k) (hu : u ≤ k)
    (hprev : ∀ s : ℕ, s ≤ k - 1 → 0 ≤ signedChain m (k - 1) s) :
    0 ≤ ((-1 : ℚ) ^ (k + t + u) * adjD k (Algebra.DiagonalObstruction.markedPoint m) 0 t u) *
      ((u * (u - 1) : ℕ) : ℚ) * signedChain m (k - 1) (u - 1) := by
  exact mul_nonneg
    (mul_nonneg (signed_adjD_marked_nonneg hk hkm ht hu) (Nat.cast_nonneg _))
    (hprev (u - 1) (by omega))

private theorem signedChain_lower (m : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k < m →
      0 < signedChain m k k ∧ ∀ t : ℕ, t ≤ k → 0 ≤ signedChain m k t := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hkm
    rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
    · subst hk1
      constructor
      · norm_num [signedChain, stageSign, clearedChain_one, varthetaOne]
      · intro t ht
        interval_cases t <;> norm_num [signedChain, stageSign, clearedChain_one, varthetaOne]
    · have hk' : 2 ≤ k := by omega
      have hprev := ih (k - 1) (by omega) (by omega) (by omega)
      have hw : (0 : ℚ) < ((k * (k - 1) : ℕ) : ℚ) := by
        exact_mod_cast Nat.mul_pos (by omega : 0 < k) (by omega : 0 < k - 1)
      constructor
      · rw [signedChain_step m hk']
        refine Finset.sum_pos' (fun u hu => signed_term_nonneg hk hkm.le (le_refl k)
          (by have := Finset.mem_range.mp hu; omega) hprev.2) ?_
        refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩
        exact mul_pos (mul_pos (signed_adjD_top_top_pos hk hkm) hw) hprev.1
      · intro t ht
        rw [signedChain_step m hk']
        exact Finset.sum_nonneg fun u hu => signed_term_nonneg hk hkm.le ht
          (by have := Finset.mem_range.mp hu; omega) hprev.2

theorem W_marked_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    W m (Algebra.DiagonalObstruction.markedPoint m) 0 ≠ 0 := by
  have hprev := signedChain_lower m (m - 1) (by omega) (by omega)
  have hw : (0 : ℚ) < ((m * (m - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < m) (by omega : 0 < m - 1)
  have hpos : 0 < signedChain m m 0 := by
    rw [signedChain_step m hm]
    refine Finset.sum_pos' (fun u hu => signed_term_nonneg (by omega) (le_refl m)
      (Nat.zero_le m) (by have := Finset.mem_range.mp hu; omega) hprev.2) ?_
    refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), ?_⟩
    exact mul_pos (mul_pos (signed_adjD_zero_top_pos m (Algebra.DiagonalObstruction.markedPoint m))
        hw) hprev.1
  intro hz
  change clearedChain (Algebra.DiagonalObstruction.markedPoint m) 0 m 0 = 0 at hz
  simp only [signedChain, hz, mul_zero, lt_self_iff_false] at hpos

end Rhone.Probability.DiagonalObstruction
