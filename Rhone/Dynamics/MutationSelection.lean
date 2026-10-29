/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Mutation–selection balance

Source: haldane1927, pp. 840–841, eq. (2.0); crow_kimura1970, §6.5; nagylaki1992, §2. -/

@[expose] public section

namespace Rhone.Dynamics

variable {F : Type*} [Field F]

def hapMutSelStep (s μ q : F) : F := μ + (1 - μ) * (q * (1 - s) / (1 - s * q))

/-- Source: felsenstein_teg2019, sec. III.5, eq. (III-18), p. 147, eq. (III-23), p. 150. -/
theorem hapMutSelStep_sub (s μ q : F) (h : 1 - s * q ≠ 0) :
    hapMutSelStep s μ q - q = (1 - q) * (μ - s * q) / (1 - s * q) := by
  simp only [hapMutSelStep]
  generalize hd : 1 - s * q = D at h ⊢
  field_simp
  rw [← hd]
  ring

/-- Source: felsenstein_teg2019, sec. III.5, eq. (III-18), p. 147, eq. (III-23), p. 150. -/
theorem hapMutSelStep_fixed {s μ : F} (hs : s ≠ 0) (hμ : μ ≠ 1) :
    hapMutSelStep s μ (μ / s) = μ / s := by
  have h : 1 - s * (μ / s) ≠ 0 := by
    rw [mul_div_cancel₀ _ hs]; exact sub_ne_zero.mpr (Ne.symm hμ)
  have := hapMutSelStep_sub s μ (μ / s) h
  rw [mul_div_cancel₀ _ hs, sub_self, mul_zero, zero_div, sub_eq_zero] at this
  exact this

theorem hapMutSelStep_eq_iff {s μ : F} (hs : s ≠ 0) {q : F} (h : 1 - s * q ≠ 0) :
    hapMutSelStep s μ q = q ↔ q = 1 ∨ q = μ / s := by
  rw [← sub_eq_zero, hapMutSelStep_sub s μ q h, div_eq_zero_iff, mul_eq_zero]
  simp only [h, or_false, sub_eq_zero, eq_div_iff hs]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (by rw [mul_comm]; exact h1.symm)
  · rintro (h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (by rw [mul_comm]; exact h1.symm)

theorem hapMutSelStep_sub_eq {s μ q : F} (hs : s ≠ 0) (h : 1 - s * q ≠ 0) :
    hapMutSelStep s μ q - μ / s = (1 - s) / (1 - s * q) * (q - μ / s) := by
  simp only [hapMutSelStep]
  generalize hd : 1 - s * q = D at h ⊢
  field_simp
  rw [← hd]
  ring

def dipMutSelStep (h s μ q : F) : F :=
  μ + (1 - μ) * (q * (1 - h * s * (1 - q) - s * q) / (1 - 2 * h * s * q * (1 - q) - s * q ^ 2))

/-- Source: crow_kimura1970, §6.5. -/
theorem dipMutSelStep_sub (h s μ q : F) (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0) :
    dipMutSelStep h s μ q - q
      = (1 - q) * (μ - s * q ^ 2 - h * s * q * (1 + μ - 2 * q))
        / (1 - 2 * h * s * q * (1 - q) - s * q ^ 2) := by
  simp only [dipMutSelStep]
  generalize hd : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 = D at hW ⊢
  field_simp
  rw [← hd]
  ring

theorem dipMutSelStep_eq_iff (h s μ q : F) (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0) :
    dipMutSelStep h s μ q = q ↔ q = 1 ∨ μ = s * q ^ 2 + h * s * q * (1 + μ - 2 * q) := by
  rw [← sub_eq_zero, dipMutSelStep_sub h s μ q hW, div_eq_zero_iff, mul_eq_zero]
  simp only [hW, or_false, sub_eq_zero]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (by linear_combination h1)
  · rintro (h1 | h1)
    · exact Or.inl h1.symm
    · exact Or.inr (by linear_combination h1)

/-- Source: haldane1927, p. 841; crow_kimura1970, §6.5. -/
theorem recessive_mutSel_fixed {s μ q : F} (hs : s ≠ 0) (hq : q ^ 2 = μ / s)
    (hW : 1 - s * q ^ 2 ≠ 0) :
    dipMutSelStep 0 s μ q = q := by
  have hW' : 1 - 2 * 0 * s * q * (1 - q) - s * q ^ 2 ≠ 0 := by simpa using hW
  rw [dipMutSelStep_eq_iff 0 s μ q hW']
  refine Or.inr ?_
  have : s * q ^ 2 = μ := by rw [hq]; field_simp
  rw [← this]; ring

theorem recessive_mutSel_fixed_iff {s μ q : F} (hs : s ≠ 0)
    (hW : 1 - s * q ^ 2 ≠ 0) :
    dipMutSelStep 0 s μ q = q ↔ q = 1 ∨ q ^ 2 = μ / s := by
  have hW' : 1 - 2 * 0 * s * q * (1 - q) - s * q ^ 2 ≠ 0 := by simpa using hW
  rw [dipMutSelStep_eq_iff 0 s μ q hW']
  simp only [eq_div_iff hs]
  constructor <;> rintro (h1 | h1)
  · exact Or.inl h1
  · exact Or.inr (by linear_combination -h1)
  · exact Or.inl h1
  · exact Or.inr (by linear_combination -h1)

section Order

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem hapMutSelStep_factor_mem_Ioo {s q : F} (hs0 : 0 < s) (hs1 : s < 1)
    (hq1 : q < 1) : 0 < (1 - s) / (1 - s * q) ∧ (1 - s) / (1 - s * q) < 1 := by
  have h1 : 0 < 1 - s := sub_pos.mpr hs1
  have h2 : s * q < s := by nlinarith
  have h3 : 0 < 1 - s * q := by linarith
  exact ⟨div_pos h1 h3, (div_lt_one h3).mpr (by linarith)⟩

theorem dip_fixed_le_of_h_le_half {h s μ q : F} (hh : 0 < h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : h ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : q ≤ μ / (h * s * (1 + μ)) := by
  rcases (dipMutSelStep_eq_iff h s μ q hW).mp hfix with h1 | h1
  · exact absurd h1 hq1.ne
  · rw [le_div_iff₀ (by positivity)]
    have h2 : 0 ≤ s * q * (q * (1 - 2 * h)) := by
      have : 0 ≤ 1 - 2 * h := by linarith
      positivity
    nlinarith

theorem dip_fixed_ge_of_half_le_h {h s μ q : F} (hh : 0 < h) (hs : 0 < s) (hμ : 0 ≤ μ)
    (hhalf : 1 / 2 ≤ h) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hW : 1 - 2 * h * s * q * (1 - q) - s * q ^ 2 ≠ 0)
    (hfix : dipMutSelStep h s μ q = q) : μ / (h * s * (1 + μ)) ≤ q := by
  rcases (dipMutSelStep_eq_iff h s μ q hW).mp hfix with h1 | h1
  · exact absurd h1 hq1.ne
  · rw [div_le_iff₀ (by positivity)]
    have h2 : 0 ≤ s * q * (q * (2 * h - 1)) := by
      have : 0 ≤ 2 * h - 1 := by linarith
      positivity
    nlinarith

end Order

end Rhone.Dynamics
