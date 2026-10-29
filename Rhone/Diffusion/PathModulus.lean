/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.InterpolatedPath
public import Rhone.Analysis.PathCompactness

/-! # Modulus of continuity of interpolated paths -/

@[expose] public section

namespace Rhone.Diffusion

open Set Analysis
open scoped NNReal

theorem interpolate_eq_floor (a : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    interpolate a u = a ⌊u⌋₊ + (u - ⌊u⌋₊) * (a (⌊u⌋₊ + 1) - a ⌊u⌋₊) := by
  have h := interpolate_add a ⌊u⌋₊ (θ := u - ⌊u⌋₊) (sub_nonneg.2 (Nat.floor_le hu))
    (by linarith [Nat.lt_floor_add_one u])
  rwa [show (⌊u⌋₊ : ℝ) + (u - ⌊u⌋₊) = u by ring] at h

theorem interpolate_of_nonpos (a : ℕ → ℝ) {u : ℝ} (hu : u ≤ 0) : interpolate a u = a 0 := by
  simp [interpolate, interpolatePrefix, Nat.ceil_eq_zero.2 hu]

theorem interpolate_mem_Icc {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    interpolate a u ∈ Icc (0 : ℝ) 1 := by
  rcases le_or_gt u 0 with hu | hu
  · rw [interpolate_of_nonpos a hu]
    exact ha 0
  · rw [interpolate_eq_floor a hu.le]
    have h0 : 0 ≤ u - ⌊u⌋₊ := sub_nonneg.2 (Nat.floor_le hu.le)
    have h1 : 0 ≤ 1 - (u - ⌊u⌋₊) := by linarith [Nat.lt_floor_add_one u]
    obtain ⟨p0, p1⟩ := ha ⌊u⌋₊
    obtain ⟨q0, q1⟩ := ha (⌊u⌋₊ + 1)
    constructor
    · nlinarith [mul_nonneg h1 p0, mul_nonneg h0 q0]
    · nlinarith [mul_nonneg h1 (sub_nonneg.2 p1), mul_nonneg h0 (sub_nonneg.2 q1)]

theorem abs_interpolate_sub_le {a : ℕ → ℝ} (ha : ∀ m, |a (m + 1) - a m| ≤ 1) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvu : v ≤ u + 1) :
    |interpolate a v - interpolate a u| ≤ v - u := by
  set m := ⌊u⌋₊
  have hm : (m : ℝ) ≤ u := Nat.floor_le hu
  have hm1 : u < m + 1 := Nat.lt_floor_add_one u
  rw [interpolate_eq_floor a hu]
  rcases le_or_gt v (m + 1) with hv | hv
  · have hv' := interpolate_add a m (θ := v - m) (by linarith) (by linarith)
    rw [show (m : ℝ) + (v - m) = v by ring] at hv'
    rw [hv', show a m + (v - m) * (a (m + 1) - a m) - (a m + (u - m) * (a (m + 1) - a m)) =
      (v - u) * (a (m + 1) - a m) by ring, abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_right (by linarith) (ha m)
  · have hv' := interpolate_add a (m + 1) (θ := v - ((m + 1 : ℕ) : ℝ)) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [show ((m + 1 : ℕ) : ℝ) + (v - ((m + 1 : ℕ) : ℝ)) = v by ring] at hv'
    rw [hv']
    have hA := abs_le.1 (ha m)
    have hB := abs_le.1 (ha (m + 1))
    have w1 : 0 ≤ (m : ℝ) + 1 - u := by linarith
    have w2 : 0 ≤ v - ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have e : a (m + 1) + (v - ((m + 1 : ℕ) : ℝ)) * (a (m + 1 + 1) - a (m + 1)) -
        (a m + (u - m) * (a (m + 1) - a m)) =
        ((m : ℝ) + 1 - u) * (a (m + 1) - a m) +
          (v - ((m + 1 : ℕ) : ℝ)) * (a (m + 1 + 1) - a (m + 1)) := by
      push_cast
      ring
    rw [e, abs_le]
    have ev : ((m : ℝ) + 1 - u) + (v - ((m + 1 : ℕ) : ℝ)) = v - u := by
      push_cast
      ring
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hA.1 w1, mul_le_mul_of_nonneg_left hB.1 w2]
    · nlinarith [mul_le_mul_of_nonneg_left hA.2 w1, mul_le_mul_of_nonneg_left hB.2 w2]

theorem abs_interpolate_sub_le' {a : ℕ → ℝ} (ha : ∀ m, |a (m + 1) - a m| ≤ 1) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : |u - v| ≤ 1) :
    |interpolate a u - interpolate a v| ≤ |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_sub_comm, abs_sub_comm u, abs_of_nonneg (sub_nonneg.2 h)]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)] at huv
    exact abs_interpolate_sub_le ha hu h (by linarith)
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    rw [abs_of_nonneg (sub_nonneg.2 h)] at huv
    exact abs_interpolate_sub_le ha hv h (by linarith)

theorem abs_blockStart_sub_le {a : ℕ → ℝ} {b L : ℕ} {ε : ℝ}
    (H : ∀ i ≤ L, ∀ k ≤ b, |a (i * b + k) - a (i * b)| ≤ ε) (d : ℕ) :
    ∀ i, i + d ≤ L + 1 → |a ((i + d) * b) - a (i * b)| ≤ d * ε := by
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hid
    have h1 := ih i (by omega)
    have h2 := H (i + d) (by omega) b le_rfl
    rw [show (i + (d + 1)) * b = (i + d) * b + b by ring]
    calc |a ((i + d) * b + b) - a (i * b)|
        ≤ |a ((i + d) * b + b) - a ((i + d) * b)| + |a ((i + d) * b) - a (i * b)| :=
          abs_sub_le _ _ _
      _ ≤ ε + d * ε := add_le_add h2 h1
      _ = ((d + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem exists_block {b L n : ℕ} (hb : 0 < b) (hn : n ≤ (L + 1) * b) :
    ∃ i ≤ L, i * b ≤ n ∧ n ≤ i * b + b := by
  have hdm := Nat.div_add_mod n b
  have hr := Nat.mod_lt n hb
  rcases le_or_gt (n / b) L with hq | hq
  · refine ⟨n / b, hq, ?_, ?_⟩
    · rw [mul_comm]
      omega
    · rw [mul_comm]
      omega
  · refine ⟨L, le_rfl, ?_, by linarith⟩
    have h1 : b * (L + 1) ≤ b * (n / b) := Nat.mul_le_mul_left b hq
    have h2 : b * (n / b) ≤ n := Nat.le.intro hdm
    have h3 : L * b ≤ b * (L + 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left b (Nat.le_succ L)
    exact h3.trans (h1.trans h2)

theorem abs_sub_le_of_block {a : ℕ → ℝ} {b L : ℕ} {ε : ℝ} (hb : 0 < b)
    (H : ∀ i ≤ L, ∀ k ≤ b, |a (i * b + k) - a (i * b)| ≤ ε) {n n' : ℕ}
    (hn : n ≤ (L + 1) * b) (hn' : n' ≤ (L + 1) * b) (h1 : n ≤ n' + 2 * b)
    (h2 : n' ≤ n + 2 * b) : |a n - a n'| ≤ 5 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (H 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  obtain ⟨i, hi, hi1, hi2⟩ := exists_block hb hn
  obtain ⟨i', hi', hi1', hi2'⟩ := exists_block hb hn'
  have hA : |a n - a (i * b)| ≤ ε := by
    have := H i hi (n - i * b) (by omega)
    rwa [Nat.add_sub_cancel' hi1] at this
  have hA' : |a n' - a (i' * b)| ≤ ε := by
    have := H i' hi' (n' - i' * b) (by omega)
    rwa [Nat.add_sub_cancel' hi1'] at this
  have hii' : i' ≤ i + 3 := by
    have : i' * b < (i + 3 + 1) * b := by nlinarith
    exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right this)
  have hi'i : i ≤ i' + 3 := by
    have : i * b < (i' + 3 + 1) * b := by nlinarith
    exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right this)
  have hS : |a (i * b) - a (i' * b)| ≤ 3 * ε := by
    rcases le_total i i' with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      have := abs_blockStart_sub_le H d i (by omega)
      rw [abs_sub_comm]
      refine this.trans ?_
      have : (d : ℝ) ≤ 3 := by exact_mod_cast (by omega : d ≤ 3)
      nlinarith
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      have := abs_blockStart_sub_le H d i' (by omega)
      refine this.trans ?_
      have : (d : ℝ) ≤ 3 := by exact_mod_cast (by omega : d ≤ 3)
      nlinarith
  calc |a n - a n'| ≤ |a n - a (i * b)| + |a (i * b) - a n'| := abs_sub_le _ _ _
    _ ≤ |a n - a (i * b)| + (|a (i * b) - a (i' * b)| + |a (i' * b) - a n'|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ ε + (3 * ε + ε) := by
        rw [abs_sub_comm (a (i' * b))]
        gcongr
    _ = 5 * ε := by ring

theorem abs_convex_four_le {w₁ w₂ w₃ w₄ x₁ x₂ x₃ x₄ D : ℝ} (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂)
    (h₃ : 0 ≤ w₃) (h₄ : 0 ≤ w₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) (k₁ : |x₁| ≤ D) (k₂ : |x₂| ≤ D)
    (k₃ : |x₃| ≤ D) (k₄ : |x₄| ≤ D) : |w₁ * x₁ + w₂ * x₂ + w₃ * x₃ + w₄ * x₄| ≤ D := by
  rw [abs_le] at *
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k₁.1 h₁, mul_le_mul_of_nonneg_left k₂.1 h₂,
      mul_le_mul_of_nonneg_left k₃.1 h₃, mul_le_mul_of_nonneg_left k₄.1 h₄]
  · nlinarith [mul_le_mul_of_nonneg_left k₁.2 h₁, mul_le_mul_of_nonneg_left k₂.2 h₂,
      mul_le_mul_of_nonneg_left k₃.2 h₃, mul_le_mul_of_nonneg_left k₄.2 h₄]

theorem abs_interpolate_sub_le_of_block {a : ℕ → ℝ} {b L : ℕ} {ε : ℝ} (hb : 2 ≤ b)
    (H : ∀ i ≤ L, ∀ k ≤ b, |a (i * b + k) - a (i * b)| ≤ ε) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hu' : u + 1 ≤ ((L + 1) * b : ℕ)) (hv' : v + 1 ≤ ((L + 1) * b : ℕ))
    (huv : |u - v| ≤ b) : |interpolate a u - interpolate a v| ≤ 5 * ε := by
  rw [interpolate_eq_floor a hu, interpolate_eq_floor a hv]
  set m := ⌊u⌋₊
  set m' := ⌊v⌋₊
  have hm : (m : ℝ) ≤ u := Nat.floor_le hu
  have hm1 : u < m + 1 := Nat.lt_floor_add_one u
  have hm' : (m' : ℝ) ≤ v := Nat.floor_le hv
  have hm1' : v < m' + 1 := Nat.lt_floor_add_one v
  have huv' := abs_le.1 huv
  have hb0 : 0 < b := by omega
  have i1 : m + 1 ≤ (L + 1) * b := by
    have : ((m + 1 : ℕ) : ℝ) ≤ ((L + 1) * b : ℕ) := by push_cast at hu' ⊢; linarith
    exact_mod_cast this
  have i2 : m' + 1 ≤ (L + 1) * b := by
    have : ((m' + 1 : ℕ) : ℝ) ≤ ((L + 1) * b : ℕ) := by push_cast at hv' ⊢; linarith
    exact_mod_cast this
  have d1 : m ≤ m' + b := by
    have : (m : ℝ) < m' + b + 1 := by linarith
    have : m < m' + b + 1 := by exact_mod_cast this
    omega
  have d2 : m' ≤ m + b := by
    have : (m' : ℝ) < m + b + 1 := by linarith
    have : m' < m + b + 1 := by exact_mod_cast this
    omega
  have P : ∀ n ∈ ({m, m + 1} : Finset ℕ), ∀ n' ∈ ({m', m' + 1} : Finset ℕ),
      |a n - a n'| ≤ 5 * ε := by
    intro n hn n' hn'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn hn'
    refine abs_sub_le_of_block hb0 H ?_ ?_ ?_ ?_ <;> omega
  set θ := u - m
  set θ' := v - m'
  have h0 : 0 ≤ θ := by simp only [θ]; linarith
  have h1 : 0 ≤ 1 - θ := by simp only [θ]; linarith
  have h0' : 0 ≤ θ' := by simp only [θ']; linarith
  have h1' : 0 ≤ 1 - θ' := by simp only [θ']; linarith
  have e : a m + θ * (a (m + 1) - a m) - (a m' + θ' * (a (m' + 1) - a m')) =
      (1 - θ) * (1 - θ') * (a m - a m') + (1 - θ) * θ' * (a m - a (m' + 1)) +
        θ * (1 - θ') * (a (m + 1) - a m') + θ * θ' * (a (m + 1) - a (m' + 1)) := by ring
  rw [e]
  exact abs_convex_four_le (mul_nonneg h1 h1') (mul_nonneg h1 h0') (mul_nonneg h0 h1')
    (mul_nonneg h0 h0') (by ring) (P _ (by simp) _ (by simp)) (P _ (by simp) _ (by simp))
    (P _ (by simp) _ (by simp)) (P _ (by simp) _ (by simp))

theorem rescaledPath_mem_Icc {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) (τ : ℝ) (t : ℝ≥0) :
    rescaledPath τ a t ∈ Icc (0 : ℝ) 1 :=
  interpolate_mem_Icc ha _

theorem modulusAt_rescaledPath_of_block {a : ℕ → ℝ} {τ d ε : ℝ} {b L j : ℕ} (hτ : 0 ≤ τ)
    (hb : 2 ≤ b) (hτd : τ * d ≤ b) (hL : τ * (j + 1) + 1 ≤ ((L + 1) * b : ℕ))
    (hε : 5 * ε ≤ 1 / (j + 1))
    (H : ∀ i ≤ L, ∀ k ≤ b, |a (i * b + k) - a (i * b)| ≤ ε) :
    ModulusAt j d (rescaledPath τ a) := by
  intro s t hs ht hst
  rw [rescaledPath_apply, rescaledPath_apply, Real.dist_eq]
  refine le_trans (abs_interpolate_sub_le_of_block hb H (mul_nonneg hτ s.2) (mul_nonneg hτ t.2)
    ?_ ?_ ?_) hε
  · linarith [mul_le_mul_of_nonneg_left hs hτ]
  · linarith [mul_le_mul_of_nonneg_left ht hτ]
  · rw [NNReal.dist_eq] at hst
    rw [← mul_sub, abs_mul, abs_of_nonneg hτ]
    exact (mul_le_mul_of_nonneg_left hst hτ).trans hτd

theorem modulusAt_rescaledPath_of_step {a : ℕ → ℝ} (ha : ∀ m, |a (m + 1) - a m| ≤ 1) {τ d : ℝ}
    {j : ℕ} (hτ : 0 ≤ τ) (hd : τ * d ≤ 1 / (j + 1)) : ModulusAt j d (rescaledPath τ a) := by
  intro s t _ _ hst
  rw [rescaledPath_apply, rescaledPath_apply, Real.dist_eq]
  rw [NNReal.dist_eq] at hst
  have hj : 1 / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have h1 : |τ * (s : ℝ) - τ * t| ≤ 1 / ((j : ℝ) + 1) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hτ]
    exact (mul_le_mul_of_nonneg_left hst hτ).trans hd
  exact (abs_interpolate_sub_le' ha (mul_nonneg hτ s.2) (mul_nonneg hτ t.2) (h1.trans hj)).trans
    h1

end Rhone.Diffusion
