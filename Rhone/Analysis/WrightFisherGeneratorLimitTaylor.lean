/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Second-order Taylor remainder on the unit interval

Source: durrett2008, ch. 7; ewens2004, ch. 4. -/

@[expose] public section

namespace Rhone.Analysis

open Set

theorem abs_unit_taylor_two_le {φ φ₁ φ₂ : ℝ → ℝ} {M : ℝ}
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ₁ s) (Icc 0 1) s)
    (h1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ₁ (φ₂ s) (Icc 0 1) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, |φ₂ s - φ₂ 0| ≤ M * s) :
    |φ 1 - φ 0 - φ₁ 0 - φ₂ 0 / 2| ≤ M / 6 := by
  have hmono : ∀ {g : ℝ → ℝ} {g' x : ℝ}, x ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt g g' (Icc 0 1) x → HasDerivWithinAt g g' (Ici x) x :=
    fun hx hg => hg.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
  have hr : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => φ₁ s - φ₁ 0 - φ₂ 0 * s) (φ₂ s - φ₂ 0) (Icc 0 1) s := by
    intro s hs
    have := ((h1 s hs).sub_const (φ₁ 0)).sub ((hasDerivWithinAt_id s (Icc 0 1)).const_mul (φ₂ 0))
    exact this.congr_deriv (by ring)
  have hB1 : ∀ x : ℝ, HasDerivWithinAt (fun s : ℝ => M * s ^ 2 / 2) (M * x) (Ici x) x := by
    intro x
    have := (((hasDerivAt_pow 2 x).const_mul M).div_const 2).hasDerivWithinAt (s := Ici x)
    exact this.congr_deriv (by norm_num; ring)
  have step1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ₁ s - φ₁ 0 - φ₂ 0 * s‖ ≤ M * s ^ 2 / 2 :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun s => φ₁ s - φ₁ 0 - φ₂ 0 * s) (f' := fun s => φ₂ s - φ₂ 0)
      (B := fun s => M * s ^ 2 / 2) (B' := fun s => M * s)
      (fun s hs => (hr s hs).continuousWithinAt)
      (fun x hx => hmono hx (hr x (Ico_subset_Icc_self hx)))
      (by simp)
      (by fun_prop)
      (fun x _ => hB1 x)
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hM x (Ico_subset_Icc_self hx))
  have hg : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => φ s - φ 0 - φ₁ 0 * s - φ₂ 0 / 2 * s ^ 2)
        (φ₁ s - φ₁ 0 - φ₂ 0 * s) (Icc 0 1) s := by
    intro s hs
    have := (((h0 s hs).sub_const (φ 0)).sub
      ((hasDerivWithinAt_id s (Icc 0 1)).const_mul (φ₁ 0))).sub
      (((hasDerivAt_pow 2 s).const_mul (φ₂ 0 / 2)).hasDerivWithinAt (s := Icc 0 1))
    exact this.congr_deriv (by norm_num; ring)
  have hB2 : ∀ x : ℝ,
      HasDerivWithinAt (fun s : ℝ => M * s ^ 3 / 6) (M * x ^ 2 / 2) (Ici x) x := by
    intro x
    have := (((hasDerivAt_pow 3 x).const_mul M).div_const 6).hasDerivWithinAt (s := Ici x)
    exact this.congr_deriv (by norm_num; ring)
  have step2 : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖φ s - φ 0 - φ₁ 0 * s - φ₂ 0 / 2 * s ^ 2‖ ≤ M * s ^ 3 / 6 :=
    image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun s => φ s - φ 0 - φ₁ 0 * s - φ₂ 0 / 2 * s ^ 2)
      (f' := fun s => φ₁ s - φ₁ 0 - φ₂ 0 * s)
      (B := fun s => M * s ^ 3 / 6) (B' := fun s => M * s ^ 2 / 2)
      (fun s hs => (hg s hs).continuousWithinAt)
      (fun x hx => hmono hx (hg x (Ico_subset_Icc_self hx)))
      (by simp)
      (by fun_prop)
      (fun x _ => hB2 x)
      (fun x hx => step1 x (Ico_subset_Icc_self hx))
  have h := step2 1 ⟨zero_le_one, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  convert h using 2 <;> ring

theorem abs_taylor_two_remainder_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc 0 1) x)
    (hf' : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Icc 0 1) x)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |f y - f x - f' x * (y - x) - f'' x / 2 * (y - x) ^ 2| ≤ L / 6 * |y - x| ^ 3 := by
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ → ℝ, γ = fun s => x + s * (y - x) := ⟨_, rfl⟩
  have e0 : γ 0 = x := by simp [hγdef]
  have e1 : γ 1 = y := by simp [hγdef]
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ Icc (0 : ℝ) 1 := by
    intro s hs
    rw [hγdef]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) hx.1, mul_nonneg hs.1 hy.1]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hx.2),
        mul_nonneg hs.1 (sub_nonneg.2 hy.2)]
  have hγd : ∀ s : ℝ, HasDerivWithinAt γ (y - x) (Icc 0 1) s := by
    intro s
    rw [hγdef]
    have := ((hasDerivWithinAt_id s (Icc (0 : ℝ) 1)).mul_const (y - x)).const_add x
    simpa using this
  have hφ : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => f (γ s)) (f' (γ s) * (y - x)) (Icc 0 1) s :=
    fun s hs => HasDerivWithinAt.comp s (hf (γ s) (hγ s hs)) (hγd s) hγ
  have hφ₁ : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => f' (γ s) * (y - x)) (f'' (γ s) * (y - x) ^ 2) (Icc 0 1) s := by
    intro s hs
    have := (HasDerivWithinAt.comp s (hf' (γ s) (hγ s hs)) (hγd s) hγ).mul_const (y - x)
    exact this.congr_deriv (by ring)
  have hM : ∀ s ∈ Icc (0 : ℝ) 1,
      |f'' (γ s) * (y - x) ^ 2 - f'' (γ 0) * (y - x) ^ 2| ≤ L * |y - x| ^ 3 * s := by
    intro s hs
    have hl := hL (γ s) (hγ s hs) (γ 0) (hγ 0 ⟨le_rfl, zero_le_one⟩)
    have hd : γ s - γ 0 = s * (y - x) := by simp [hγdef]
    rw [hd, abs_mul, abs_of_nonneg hs.1] at hl
    calc |f'' (γ s) * (y - x) ^ 2 - f'' (γ 0) * (y - x) ^ 2|
        = |f'' (γ s) - f'' (γ 0)| * (y - x) ^ 2 := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (y - x))]
      _ ≤ L * (s * |y - x|) * (y - x) ^ 2 := by gcongr
      _ = L * |y - x| ^ 3 * s := by
          rw [← sq_abs (y - x)]
          ring
  have key := abs_unit_taylor_two_le (φ := fun s => f (γ s))
    (φ₁ := fun s => f' (γ s) * (y - x)) (φ₂ := fun s => f'' (γ s) * (y - x) ^ 2) hφ hφ₁ hM
  simp only [e0, e1] at key
  convert key using 2 <;> ring

end Rhone.Analysis
