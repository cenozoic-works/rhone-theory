/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.MutationSelection
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Mutation-selection balance: two-sided bounds on the diploid equilibrium

Source: haldane1927, p. 841; felsenstein_teg2019, sec. III.5, eq. (III-23), p. 150; crow_kimura1970,
sec. 6.5. -/

@[expose] public section

namespace Rhone.Dynamics

section Order

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem dip_fixed_quadratic {h s μ q : F} (hq1 : q ≠ 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) :
    s * (1 - 2 * h) * q ^ 2 + h * s * (1 + μ) * q = μ := by
  rcases (dipMutSelStep_eq_iff h s μ q hW).mp hfix with h1 | h1
  · exact absurd h1 hq1
  · linear_combination -h1

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_ge_of_h_le_half {h s μ q : F} (hh : 0 ≤ h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : h ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : μ / (s * (1 - h + h * μ)) ≤ q := by
  have hQ := dip_fixed_quadratic hq1.ne hW hfix
  have hc : 0 ≤ s * (1 - 2 * h) := mul_nonneg hs.le (by linarith)
  have hd : 0 < s * (1 - h + h * μ) := by
    have h0 := mul_nonneg hh hμ
    have : 0 < 1 - h + h * μ := by linarith
    exact mul_pos hs this
  rw [div_le_iff₀ hd]
  nlinarith [mul_nonneg hc (mul_nonneg hq0 (sub_nonneg.mpr hq1.le))]

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_bounds_of_h_le_half {h s μ q : F} (hh : 0 < h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : h ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) :
    μ / (s * (1 - h + h * μ)) ≤ q ∧ q ≤ μ / (h * s * (1 + μ)) :=
  ⟨dip_fixed_ge_of_h_le_half hh.le hs hμ hhalf hq0 hq1 hW hfix,
    dip_fixed_le_of_h_le_half hh hs hμ hhalf hq0 hq1 hW hfix⟩

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_mul_le_of_half_le_h {h s μ q : F} (hs : 0 < s)
    (hhalf : 1 / 2 ≤ h) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : s * (1 - h + h * μ) * q ≤ μ := by
  have hQ := dip_fixed_quadratic hq1.ne hW hfix
  have hc : 0 ≤ s * (2 * h - 1) := mul_nonneg hs.le (by linarith)
  nlinarith [mul_nonneg hc (mul_nonneg hq0 (sub_nonneg.mpr hq1.le))]

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_le_of_half_le_h_le_one {h s μ q : F} (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : 1 / 2 ≤ h) (hh1 : h ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : q ≤ μ / (s * (1 - h + h * μ)) := by
  have hm := dip_fixed_mul_le_of_half_le_h hs hhalf hq0 hq1 hW hfix
  have hhμ : 0 ≤ h * μ := mul_nonneg (by linarith) hμ
  have hk : 0 ≤ 1 - h + h * μ := by linarith
  rcases hk.lt_or_eq with hk | hk
  · rw [le_div_iff₀ (mul_pos hs hk)]
    calc q * (s * (1 - h + h * μ)) = s * (1 - h + h * μ) * q := by ring
      _ ≤ μ := hm
  · have hh1' : h = 1 := by linarith
    have hμ' : μ = 0 := by
      have : h * μ = 0 := by linarith
      rwa [hh1', one_mul] at this
    have hQ := dip_fixed_quadratic hq1.ne hW hfix
    rw [hh1', hμ'] at hQ
    have hprod : s * q * (1 - q) = 0 := by linear_combination hQ
    have hq : q = 0 := by
      rcases mul_eq_zero.mp hprod with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hs.ne'
        · exact h3
      · exact absurd (sub_eq_zero.mp h2).symm hq1.ne
    rw [← hk, mul_zero, div_zero]
    exact hq.le

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_bounds_of_half_le_h {h s μ q : F} (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : 1 / 2 ≤ h) (hh1 : h ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) :
    μ / (h * s * (1 + μ)) ≤ q ∧ q ≤ μ / (s * (1 - h + h * μ)) :=
  ⟨dip_fixed_ge_of_half_le_h (by linarith) hs hμ hhalf hq0 hq1 hW hfix,
    dip_fixed_le_of_half_le_h_le_one hs hμ hhalf hh1 hq0 hq1 hW hfix⟩

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_sharp_ge_of_h_le_half {h s μ q : F} (hh : 0 < h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : h ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) :
    μ / (h * s * (1 + μ)) - (1 - 2 * h) * μ ^ 2 / (h ^ 3 * s ^ 2 * (1 + μ) ^ 3) ≤ q := by
  have hQ := dip_fixed_quadratic hq1.ne hW hfix
  have h1μ : 0 < 1 + μ := by linarith
  have hb : 0 < h * s * (1 + μ) := by positivity
  have hup := dip_fixed_le_of_h_le_half hh hs hμ hhalf hq0 hq1 hW hfix
  rw [le_div_iff₀ hb] at hup
  have hbq0 : 0 ≤ h * s * (1 + μ) * q := by positivity
  have hbq : h * s * (1 + μ) * q ≤ μ := by
    calc h * s * (1 + μ) * q = q * (h * s * (1 + μ)) := by ring
      _ ≤ μ := hup
  have hsq : (h * s * (1 + μ) * q) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ hbq0 hbq 2
  have hc : 0 ≤ s * (1 - 2 * h) := mul_nonneg hs.le (by linarith)
  have e : (h * s * (1 + μ)) ^ 3 * q
      = (h * s * (1 + μ)) ^ 2 * μ - s * (1 - 2 * h) * (h * s * (1 + μ) * q) ^ 2 := by
    linear_combination (h * s * (1 + μ)) ^ 2 * hQ
  have key : (h * s * (1 + μ)) ^ 2 * μ - s * (1 - 2 * h) * μ ^ 2
      ≤ (h * s * (1 + μ)) ^ 3 * q := by
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hsq hc]
  have hh' : h ≠ 0 := hh.ne'
  have hs' : s ≠ 0 := hs.ne'
  have hμ' : 1 + μ ≠ 0 := h1μ.ne'
  have eq : μ / (h * s * (1 + μ)) - (1 - 2 * h) * μ ^ 2 / (h ^ 3 * s ^ 2 * (1 + μ) ^ 3)
      = ((h * s * (1 + μ)) ^ 2 * μ - s * (1 - 2 * h) * μ ^ 2) / (h * s * (1 + μ)) ^ 3 := by
    field_simp
  rw [eq, div_le_iff₀ (by positivity)]
  linarith [key]

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_sharp_le_of_half_le_h {h s μ q : F} (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : 1 / 2 ≤ h) (hh1 : h ≤ 1) (hq0 : 0 ≤ q) (hq2 : q ≤ 1 / 2)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) :
    q ≤ μ / (h * s * (1 + μ)) + 4 * (2 * h - 1) * μ ^ 2 / (h ^ 3 * s ^ 2 * (1 + μ) ^ 3) := by
  have hq1 : q < 1 := by linarith
  have hh : 0 < h := by linarith
  have hQ := dip_fixed_quadratic hq1.ne hW hfix
  have h1μ : 0 < 1 + μ := by linarith
  have hb : 0 < h * s * (1 + μ) := by positivity
  have hc : 0 ≤ s * (2 * h - 1) := mul_nonneg hs.le (by linarith)
  have hk : 0 ≤ s * (1 - h + h * μ) := by
    have : 0 ≤ h * μ := mul_nonneg hh.le hμ
    exact mul_nonneg hs.le (by linarith)
  have hgap : 0 ≤ h * s * (1 + μ) - 2 * (s * (2 * h - 1)) * q := by
    nlinarith [mul_nonneg hc (by linarith : (0 : F) ≤ 1 - 2 * q)]
  have hbq0 : 0 ≤ h * s * (1 + μ) * q := by positivity
  have hbq : h * s * (1 + μ) * q ≤ 2 * μ := by
    nlinarith [mul_nonneg hq0 hgap]
  have hsq : (h * s * (1 + μ) * q) ^ 2 ≤ (2 * μ) ^ 2 := pow_le_pow_left₀ hbq0 hbq 2
  have e : (h * s * (1 + μ)) ^ 3 * q
      = (h * s * (1 + μ)) ^ 2 * μ + s * (2 * h - 1) * (h * s * (1 + μ) * q) ^ 2 := by
    linear_combination (h * s * (1 + μ)) ^ 2 * hQ
  have key : (h * s * (1 + μ)) ^ 3 * q
      ≤ (h * s * (1 + μ)) ^ 2 * μ + 4 * (s * (2 * h - 1)) * μ ^ 2 := by
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hsq hc]
  have hh' : h ≠ 0 := hh.ne'
  have hs' : s ≠ 0 := hs.ne'
  have hμ' : 1 + μ ≠ 0 := h1μ.ne'
  have eq : μ / (h * s * (1 + μ)) + 4 * (2 * h - 1) * μ ^ 2 / (h ^ 3 * s ^ 2 * (1 + μ) ^ 3)
      = ((h * s * (1 + μ)) ^ 2 * μ + 4 * (s * (2 * h - 1)) * μ ^ 2) / (h * s * (1 + μ)) ^ 3 := by
    field_simp
  rw [eq, le_div_iff₀ (by positivity)]
  linarith [key]

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_eq_of_h_eq_half {s μ q : F} (hs : s ≠ 0) (hμ : 1 + μ ≠ 0) (hq1 : q ≠ 1)
    (hW : 1 - 2 * (1 / 2) * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep (1 / 2) s μ q = q) : q = 2 * μ / (s * (1 + μ)) := by
  have hQ := dip_fixed_quadratic hq1 hW hfix
  rw [eq_div_iff (mul_ne_zero hs hμ)]
  linear_combination 2 * hQ

theorem dip_fixed_sq_sub {h s μ q : F} (hs : s ≠ 0) (hq1 : q ≠ 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : q ^ 2 - μ / s = h * q * (2 * q - 1 - μ) := by
  have hQ := dip_fixed_quadratic hq1 hW hfix
  have hd : μ / s = q ^ 2 - h * q * (2 * q - 1 - μ) := by
    rw [div_eq_iff hs]
    linear_combination -hQ
  rw [hd]
  ring

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_abs_sq_sub_le {h s μ q : F} (hh : 0 ≤ h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : |q ^ 2 - μ / s| ≤ h * (1 + μ) * q := by
  rw [dip_fixed_sq_sub hs.ne' hq1.ne hW hfix, abs_le]
  have hhq : 0 ≤ h * q := mul_nonneg hh hq0
  constructor
  · nlinarith [mul_nonneg hhq (by linarith : (0 : F) ≤ 2 * q)]
  · nlinarith [mul_nonneg hhq (by linarith : (0 : F) ≤ 2 - 2 * q + 2 * μ)]

end Order

/-- Source: crow_kimura1970, sec. 6.5. -/
theorem dip_fixed_abs_sub_sqrt_le {h s μ q : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : |q - Real.sqrt (μ / s)| ≤ h * (1 + μ) := by
  have hb := dip_fixed_abs_sq_sub_le hh hs hμ hq0 hq1 hW hfix
  suffices H : ∀ r : ℝ, 0 ≤ r → r ^ 2 = μ / s → |q - r| ≤ h * (1 + μ) from
    H _ (Real.sqrt_nonneg _) (Real.sq_sqrt (div_nonneg hμ hs.le))
  intro r hr0 hr2
  rw [← hr2] at hb
  have hK : 0 ≤ h * (1 + μ) := mul_nonneg hh (by linarith)
  rw [abs_le] at hb ⊢
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · by_contra hcon
    rw [not_le] at hcon
    have hqr : 0 < q + r := by linarith
    have hp := mul_pos (by linarith : (0 : ℝ) < r - q - h * (1 + μ)) hqr
    nlinarith [mul_nonneg hK hr0]
  · by_contra hcon
    rw [not_le] at hcon
    have hqr : 0 < q + r := by linarith
    have hp := mul_pos (by linarith : (0 : ℝ) < q - r - h * (1 + μ)) hqr
    nlinarith [mul_nonneg hK hr0]

/-- Source: haldane1927, p. 841; crow_kimura1970, sec. 6.5. -/
theorem recessive_mutSel_fixed_eq_sqrt {s μ q : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hW : 1 - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep 0 s μ q = q) : q = Real.sqrt (μ / s) := by
  have hW' : 1 - 2 * 0 * s * q * (1 - q) - s * q ^ 2 ≠ 0 := by simpa using hW
  have h2 := dip_fixed_abs_sub_sqrt_le le_rfl hs hμ hq0 hq1 hW' hfix
  rw [zero_mul] at h2
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h2)

theorem exists_dip_fixed_gt_div_of_half_le_h :
    ∃ h s μ q : ℝ, 1 / 2 ≤ h ∧ 0 < s ∧ 0 ≤ μ ∧ 0 ≤ q ∧ q < 1 ∧
      1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0 ∧ dipMutSelStep h s μ q = q ∧
      μ / (s * (1 - h + h * μ)) < q := by
  refine ⟨3 / 2, 1 / 2, 13 / 185, 1 / 10, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, by norm_num⟩
  unfold dipMutSelStep
  norm_num

theorem exists_dip_fixed_gt_sharp_of_half_le_h_le_one :
    ∃ h s μ q : ℝ, 1 / 2 ≤ h ∧ h ≤ 1 ∧ 0 < s ∧ 0 ≤ μ ∧ 0 ≤ q ∧ q < 1 ∧
      1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0 ∧ dipMutSelStep h s μ q = q ∧
      μ / (h * s * (1 + μ)) + 4 * (2 * h - 1) * μ ^ 2 / (h ^ 3 * s ^ 2 * (1 + μ) ^ 3) < q := by
  refine ⟨1, 1 / 2, 99 / 10100, 99 / 100, by norm_num, le_rfl, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  unfold dipMutSelStep
  norm_num

end Rhone.Dynamics
