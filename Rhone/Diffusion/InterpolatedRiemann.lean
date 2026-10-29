/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.PathModulus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Riemann sums along an interpolated path with small steps -/

@[expose] public section

namespace Rhone.Diffusion

open Set MeasureTheory

theorem abs_interpolate_sub_ceil_le {a : ℕ → ℝ} {η : ℝ} (hη : 0 ≤ η) {u : ℝ}
    (hstep : ∀ l < ⌈u⌉₊, |a (l + 1) - a l| ≤ η) : |interpolate a u - a ⌈u⌉₊| ≤ η := by
  rcases Nat.eq_zero_or_pos ⌈u⌉₊ with h0 | hpos
  · have hu : u ≤ 0 := Nat.ceil_eq_zero.1 h0
    rw [interpolate_of_nonpos a hu, h0, sub_self, abs_zero]
    exact hη
  · obtain ⟨j, hj⟩ : ∃ j, ⌈u⌉₊ = j + 1 := ⟨⌈u⌉₊ - 1, by omega⟩
    have hlt : (j : ℝ) < u := Nat.lt_ceil.1 (by omega)
    have hle : u ≤ (j : ℝ) + 1 := by
      have := Nat.le_ceil u
      rw [hj] at this
      exact_mod_cast this
    have h := interpolate_add a j (θ := u - j) (by linarith) (by linarith)
    rw [show (j : ℝ) + (u - j) = u by ring] at h
    rw [h, hj]
    have hs := hstep j (by omega)
    have e : a j + (u - j) * (a (j + 1) - a j) - a (j + 1) = (u - j - 1) * (a (j + 1) - a j) := by
      ring
    rw [e, abs_mul]
    have h1 : |u - j - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |u - j - 1| * |a (j + 1) - a j| ≤ 1 * |a (j + 1) - a j| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ η := by rw [one_mul]; exact hs

theorem continuous_comp_interpolate {g : ℝ → ℝ} (hg : Continuous g) (a : ℕ → ℝ) (τ : ℝ) :
    Continuous fun u => g (interpolate a (τ * u)) :=
  hg.comp ((continuous_interpolate a).comp (continuous_const.mul continuous_id))

theorem abs_integral_cell_sub_le {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) {τ : ℝ}
    (hτ : 0 < τ) {l : ℕ} {η ε : ℝ} (hs : |a (l + 1) - a l| ≤ η) {g : ℝ → ℝ}
    (hgc : Continuous g)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ η → |g x - g y| ≤ ε) :
    |(∫ u in (l : ℝ) / τ..((l + 1 : ℕ) : ℝ) / τ, g (interpolate a (τ * u))) - g (a l) / τ| ≤
      ε / τ := by
  have hlt : (l : ℝ) / τ ≤ ((l + 1 : ℕ) : ℝ) / τ := by
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hτ.le
  have hcont := continuous_comp_interpolate hgc a τ
  have hdiff : ((l + 1 : ℕ) : ℝ) / τ - (l : ℝ) / τ = 1 / τ := by
    rw [div_sub_div_same]
    push_cast
    ring_nf
  have hconst : ∫ _u in (l : ℝ) / τ..((l + 1 : ℕ) : ℝ) / τ, g (a l) = g (a l) / τ := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hdiff, one_div_mul_eq_div]
  rw [← hconst, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
    intervalIntegrable_const]
  have hb : |((l + 1 : ℕ) : ℝ) / τ - (l : ℝ) / τ| = 1 / τ := by
    rw [hdiff, abs_of_pos (one_div_pos.2 hτ)]
  have key := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (l : ℝ) / τ) (b := ((l + 1 : ℕ) : ℝ) / τ) (C := ε)
    (f := fun u => g (interpolate a (τ * u)) - g (a l)) (fun u hu => ?_)
  · rw [Real.norm_eq_abs, hb] at key
    calc _ ≤ ε * (1 / τ) := key
      _ = ε / τ := by ring
  · rw [uIoc_of_le hlt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have h1 : (l : ℝ) < τ * u := by
      rw [div_lt_iff₀ hτ] at hu1
      linarith
    have h2 : τ * u ≤ (l : ℝ) + 1 := by
      rw [le_div_iff₀ hτ] at hu2
      push_cast at hu2
      linarith
    have hX := interpolate_add a l (θ := τ * u - l) (by linarith) (by linarith)
    rw [show (l : ℝ) + (τ * u - l) = τ * u by ring] at hX
    rw [Real.norm_eq_abs]
    refine hg _ (interpolate_mem_Icc ha _) _ (ha l) ?_
    rw [hX, add_sub_cancel_left, abs_mul]
    have hθ : |τ * u - l| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |τ * u - l| * |a (l + 1) - a l| ≤ 1 * |a (l + 1) - a l| :=
          mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      _ ≤ η := by rw [one_mul]; exact hs

theorem abs_integral_block_sub_le {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) {τ : ℝ}
    (hτ : 0 < τ) (k n : ℕ) {η ε : ℝ} (hs : ∀ i < n, |a (k + i + 1) - a (k + i)| ≤ η)
    {g : ℝ → ℝ} (hgc : Continuous g)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ η → |g x - g y| ≤ ε) :
    |(∫ u in (k : ℝ) / τ..((k + n : ℕ) : ℝ) / τ, g (interpolate a (τ * u))) -
      (∑ i ∈ Finset.range n, g (a (k + i))) / τ| ≤ n * ε / τ := by
  have hcont := continuous_comp_interpolate hgc a τ
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun u => g (interpolate a (τ * u))) (a := fun i : ℕ => ((k + i : ℕ) : ℝ) / τ) (n := n)
    (fun i _ => hcont.intervalIntegrable _ _)
  simp only [add_zero] at hsum
  rw [← hsum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range n, |(∫ u in ((k + i : ℕ) : ℝ) / τ..((k + (i + 1) : ℕ) : ℝ) / τ,
        g (interpolate a (τ * u))) - g (a (k + i)) / τ|
      ≤ ∑ _i ∈ Finset.range n, ε / τ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h := abs_integral_cell_sub_le ha hτ (l := k + i)
          (hs i (Finset.mem_range.1 hi)) hgc hg
        rwa [show k + (i + 1) = k + i + 1 by ring]
    _ = n * ε / τ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem abs_integral_interpolate_sub_sum_le {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1)
    {τ : ℝ} (hτ : 0 < τ) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) {η ε G : ℝ}
    (hstep : ∀ l < ⌈τ * t⌉₊, |a (l + 1) - a l| ≤ η) {g : ℝ → ℝ} (hgc : Continuous g)
    (hG : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ G)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ η → |g x - g y| ≤ ε) :
    |(∫ u in s..t, g (interpolate a (τ * u))) -
      (∑ l ∈ Finset.Ico ⌈τ * s⌉₊ ⌈τ * t⌉₊, g (a l)) / τ| ≤
      ((⌈τ * t⌉₊ : ℝ) - ⌈τ * s⌉₊) * ε / τ + 2 * G / τ := by
  set k := ⌈τ * s⌉₊ with hk
  set m := ⌈τ * t⌉₊ with hm
  have hτs : 0 ≤ τ * s := mul_nonneg hτ.le hs0
  have hτt : 0 ≤ τ * t := mul_nonneg hτ.le (hs0.trans hst)
  have hkm : k ≤ m := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst hτ.le)
  have hk1 : τ * s ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < τ * s + 1 := Nat.ceil_lt_add_one hτs
  have hm1 : τ * t ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < τ * t + 1 := Nat.ceil_lt_add_one hτt
  have hcont := continuous_comp_interpolate hgc a τ
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : ∀ u, ‖g (interpolate a (τ * u))‖ ≤ G := fun u => by
    rw [Real.norm_eq_abs]
    exact hG _ (interpolate_mem_Icc ha _)
  have hblock := abs_integral_block_sub_le ha hτ k (m - k) (η := η) (ε := ε)
    (fun i hi => hstep (k + i) (by omega)) hgc hg
  rw [show k + (m - k) = m by omega] at hblock
  have hsumeq : ∑ l ∈ Finset.Ico k m, g (a l) = ∑ i ∈ Finset.range (m - k), g (a (k + i)) :=
    Finset.sum_Ico_eq_sum_range _ _ _
  have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hkm
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := (k : ℝ) / τ) (C := G) (f := fun u => g (interpolate a (τ * u)))
    (fun u _ => hbound u)
  have hright := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (m : ℝ) / τ) (b := t) (C := G) (f := fun u => g (interpolate a (τ * u)))
    (fun u _ => hbound u)
  have hl1 : |(k : ℝ) / τ - s| ≤ 1 / τ := by
    have e : (k : ℝ) / τ - s = ((k : ℝ) - τ * s) / τ := by field_simp
    rw [e, abs_div, abs_of_pos hτ, div_le_div_iff_of_pos_right hτ, abs_le]
    constructor <;> linarith
  have hr1 : |t - (m : ℝ) / τ| ≤ 1 / τ := by
    have e : t - (m : ℝ) / τ = (τ * t - m) / τ := by field_simp
    rw [e, abs_div, abs_of_pos hτ, div_le_div_iff_of_pos_right hτ, abs_le]
    constructor <;> linarith
  have hsplit : (∫ u in s..t, g (interpolate a (τ * u))) =
      (∫ u in s..(k : ℝ) / τ, g (interpolate a (τ * u))) +
        (∫ u in (k : ℝ) / τ..(m : ℝ) / τ, g (interpolate a (τ * u))) +
        (∫ u in (m : ℝ) / τ..t, g (interpolate a (τ * u))) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  rw [Real.norm_eq_abs] at hleft hright
  rw [hsplit, hsumeq]
  rw [hcast] at hblock
  have hL : |∫ u in s..(k : ℝ) / τ, g (interpolate a (τ * u))| ≤ G / τ := by
    calc _ ≤ G * |(k : ℝ) / τ - s| := hleft
      _ ≤ G * (1 / τ) := mul_le_mul_of_nonneg_left hl1 hG0
      _ = G / τ := by ring
  have hR : |∫ u in (m : ℝ) / τ..t, g (interpolate a (τ * u))| ≤ G / τ := by
    calc _ ≤ G * |t - (m : ℝ) / τ| := hright
      _ ≤ G * (1 / τ) := mul_le_mul_of_nonneg_left hr1 hG0
      _ = G / τ := by ring
  have e : ∀ A B C D : ℝ, A + B + C - D = A + (B - D) + C := fun A B C D => by ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  have h2 : 2 * G / τ = G / τ + G / τ := by ring
  rw [h2]
  linarith

theorem abs_martingale_defect_le {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) {τ : ℝ}
    (hτ : 1 ≤ τ) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) {η ε Bf Bg : ℝ} (hη : 0 < η)
    (hε : 0 ≤ ε) {f g : ℝ → ℝ} (hgc : Continuous g) (hBf : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ Bf)
    (hBg : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ Bg) (hBgτ : 2 * Bg / τ ≤ ε)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ η → |f x - f y| ≤ ε)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ η → |g x - g y| ≤ ε)
    (err : ℕ → ℝ) (herr : ∀ l, |err l| ≤ ε) :
    |(f (interpolate a (τ * t)) - f (interpolate a (τ * s)) -
        ∫ u in s..t, g (interpolate a (τ * u))) -
      (f (a ⌈τ * t⌉₊) - f (a ⌈τ * s⌉₊) -
        ∑ l ∈ Finset.Ico ⌈τ * s⌉₊ ⌈τ * t⌉₊, (g (a l) + err l) / τ)| ≤
      (2 * t + 5) * ε + (4 * Bf + (2 * t + 1) * Bg + (t + 1) * ε) *
        ∑ l ∈ Finset.range ⌈τ * t⌉₊, (a (l + 1) - a l) ^ 4 / η ^ 4 := by
  set k := ⌈τ * s⌉₊ with hk
  set m := ⌈τ * t⌉₊ with hm
  have hτ0 : 0 < τ := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst
  have hτs : 0 ≤ τ * s := mul_nonneg hτ0.le hs0
  have hτt : 0 ≤ τ * t := mul_nonneg hτ0.le ht0
  have hkm : k ≤ m := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst hτ0.le)
  have hk1 : τ * s ≤ k := Nat.le_ceil _
  have hm2 : (m : ℝ) < τ * t + 1 := Nat.ceil_lt_add_one hτt
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0 ⟨le_rfl, zero_le_one⟩)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0 ⟨le_rfl, zero_le_one⟩)
  have hmk : ((m : ℝ) - k) / τ ≤ t + 1 := by
    rw [div_le_iff₀ hτ0]
    have e : (t + 1) * τ = τ * t + τ := by ring
    linarith
  have hcard : ((Finset.Ico k m).card : ℝ) = (m : ℝ) - k := by
    rw [Nat.card_Ico, Nat.cast_sub hkm]
  have hsplit : ∑ l ∈ Finset.Ico k m, (g (a l) + err l) / τ =
      (∑ l ∈ Finset.Ico k m, g (a l)) / τ + (∑ l ∈ Finset.Ico k m, err l) / τ := by
    rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
  have hsum_le : ∀ (c : ℝ) (v : ℕ → ℝ), (∀ l, |v l| ≤ c) →
      |(∑ l ∈ Finset.Ico k m, v l) / τ| ≤ (t + 1) * c := by
    intro c v hv
    have hc : 0 ≤ c := (abs_nonneg _).trans (hv 0)
    rw [abs_div, abs_of_pos hτ0]
    have h1 : |∑ l ∈ Finset.Ico k m, v l| ≤ ((m : ℝ) - k) * c := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ Finset.Ico k m, |v l| ≤ ∑ _l ∈ Finset.Ico k m, c :=
            Finset.sum_le_sum fun l _ => hv l
        _ = ((m : ℝ) - k) * c := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    calc |∑ l ∈ Finset.Ico k m, v l| / τ ≤ ((m : ℝ) - k) * c / τ :=
          div_le_div_of_nonneg_right h1 hτ0.le
      _ = ((m : ℝ) - k) / τ * c := by ring
      _ ≤ (t + 1) * c := mul_le_mul_of_nonneg_right hmk hc
  have hT4 := hsum_le ε err herr
  have hS0 : 0 ≤ ∑ l ∈ Finset.range m, (a (l + 1) - a l) ^ 4 / η ^ 4 :=
    Finset.sum_nonneg fun l _ => by positivity
  have hXt := interpolate_mem_Icc ha (τ * t)
  have hXs := interpolate_mem_Icc ha (τ * s)
  rw [hsplit]
  by_cases hgood : ∀ l < m, |a (l + 1) - a l| ≤ η
  · have h1 : |f (interpolate a (τ * t)) - f (a m)| ≤ ε :=
      hf _ hXt _ (ha m) (abs_interpolate_sub_ceil_le hη.le hgood)
    have h2 : |f (interpolate a (τ * s)) - f (a k)| ≤ ε :=
      hf _ hXs _ (ha k) (abs_interpolate_sub_ceil_le hη.le fun l hl =>
        hgood l (lt_of_lt_of_le hl hkm))
    have h3 := abs_integral_interpolate_sub_sum_le ha hτ0 hs0 hst hgood hgc hBg hg
    have h3' : ((m : ℝ) - k) * ε / τ ≤ (t + 1) * ε := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right hmk hε
    have hT3 : |(∫ u in s..t, g (interpolate a (τ * u))) -
        (∑ l ∈ Finset.Ico k m, g (a l)) / τ| ≤ (t + 1) * ε + ε := by linarith
    have e : (f (interpolate a (τ * t)) - f (interpolate a (τ * s)) -
        ∫ u in s..t, g (interpolate a (τ * u))) -
        (f (a m) - f (a k) - ((∑ l ∈ Finset.Ico k m, g (a l)) / τ +
          (∑ l ∈ Finset.Ico k m, err l) / τ)) =
        (f (interpolate a (τ * t)) - f (a m)) - (f (interpolate a (τ * s)) - f (a k)) -
          ((∫ u in s..t, g (interpolate a (τ * u))) - (∑ l ∈ Finset.Ico k m, g (a l)) / τ) +
          (∑ l ∈ Finset.Ico k m, err l) / τ := by ring
    rw [e]
    have hK : 0 ≤ (4 * Bf + (2 * t + 1) * Bg + (t + 1) * ε) *
        ∑ l ∈ Finset.range m, (a (l + 1) - a l) ^ 4 / η ^ 4 :=
      mul_nonneg (by positivity) hS0
    obtain ⟨a1, b1⟩ := abs_le.1 h1
    obtain ⟨a2, b2⟩ := abs_le.1 h2
    obtain ⟨a3, b3⟩ := abs_le.1 hT3
    obtain ⟨a4, b4⟩ := abs_le.1 hT4
    rw [abs_le]
    constructor <;> linarith
  · push Not at hgood
    obtain ⟨l, hl, hbig⟩ := hgood
    have hone : 1 ≤ ∑ l ∈ Finset.range m, (a (l + 1) - a l) ^ 4 / η ^ 4 := by
      have hη4 : 0 < η ^ 4 := pow_pos hη 4
      have h1 : η ^ 4 ≤ (a (l + 1) - a l) ^ 4 := by
        have := pow_le_pow_left₀ hη.le hbig.le 4
        rwa [Even.pow_abs (by decide)] at this
      have h2 : 1 ≤ (a (l + 1) - a l) ^ 4 / η ^ 4 := (one_le_div hη4).2 h1
      exact h2.trans (Finset.single_le_sum (f := fun l => (a (l + 1) - a l) ^ 4 / η ^ 4)
        (fun _ _ => by positivity) (Finset.mem_range.2 hl))
    have hft := hBf _ hXt
    have hfs := hBf _ hXs
    have hfm := hBf _ (ha m)
    have hfk := hBf _ (ha k)
    have hint : |∫ u in s..t, g (interpolate a (τ * u))| ≤ Bg * t := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := Bg)
        (f := fun u => g (interpolate a (τ * u)))
        (fun u _ => by rw [Real.norm_eq_abs]; exact hBg _ (interpolate_mem_Icc ha _))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at h
      calc _ ≤ Bg * (t - s) := h
        _ ≤ Bg * t := mul_le_mul_of_nonneg_left (by linarith) hBg0
    have hT3 := hsum_le Bg (fun l => g (a l)) fun l => hBg _ (ha l)
    have hK1 : 0 ≤ 4 * Bf + (2 * t + 1) * Bg + (t + 1) * ε := by positivity
    have hKS : 4 * Bf + (2 * t + 1) * Bg + (t + 1) * ε ≤
        (4 * Bf + (2 * t + 1) * Bg + (t + 1) * ε) *
          ∑ l ∈ Finset.range m, (a (l + 1) - a l) ^ 4 / η ^ 4 :=
      le_mul_of_one_le_right hK1 hone
    have h25 : 0 ≤ (2 * t + 5) * ε := by positivity
    have hBgt : Bg * t + (t + 1) * Bg = (2 * t + 1) * Bg := by ring
    obtain ⟨a1, b1⟩ := abs_le.1 hft
    obtain ⟨a2, b2⟩ := abs_le.1 hfs
    obtain ⟨a3, b3⟩ := abs_le.1 hfm
    obtain ⟨a4, b4⟩ := abs_le.1 hfk
    obtain ⟨a5, b5⟩ := abs_le.1 hint
    obtain ⟨a6, b6⟩ := abs_le.1 hT3
    obtain ⟨a7, b7⟩ := abs_le.1 hT4
    rw [abs_le]
    constructor <;> linarith

end Rhone.Diffusion
