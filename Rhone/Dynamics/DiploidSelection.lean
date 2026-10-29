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
# One-locus viability selection with two alleles

Source: fisher1922, sec. 1, p. 324; wright1937, pp. 307–308, eq. (1); crow_kimura1970, ch. 6;
nagylaki1992, sec. 4.1, eq. (4.17)–(4.18), (4.26), pp. 50–51; felsenstein_teg2019, sec. II.8, eq.
(II-101), p. 84. -/

@[expose] public section

namespace Rhone.Dynamics

variable {F : Type*} [Field F]

def meanFit (w11 w12 w22 p : F) : F :=
  p ^ 2 * w11 + 2 * p * (1 - p) * w12 + (1 - p) ^ 2 * w22

def selStep (w11 w12 w22 p : F) : F :=
  (p ^ 2 * w11 + p * (1 - p) * w12) / meanFit w11 w12 w22 p

def selBracket (w11 w12 w22 p : F) : F := p * (w11 - w12) + (1 - p) * (w12 - w22)

def polyEq (w11 w12 w22 : F) : F := (w12 - w22) / (2 * w12 - w11 - w22)

/-- Source: crow_kimura1970, eq. 6.2.2. -/
theorem selStep_sub (w11 w12 w22 p : F) (h : meanFit w11 w12 w22 p ≠ 0) :
    selStep w11 w12 w22 p - p
      = p * (1 - p) * selBracket w11 w12 w22 p / meanFit w11 w12 w22 p := by
  simp only [selStep, selBracket]
  field_simp
  simp only [meanFit]
  ring

theorem selBracket_eq (w11 w12 w22 p : F) :
    selBracket w11 w12 w22 p = (w12 - w22) - p * (2 * w12 - w11 - w22) := by
  simp only [selBracket]; ring

theorem meanFit_selStep_sub (w11 w12 w22 p : F) (h : meanFit w11 w12 w22 p ≠ 0) :
    meanFit w11 w12 w22 (selStep w11 w12 w22 p) - meanFit w11 w12 w22 p
      = p * (1 - p) * selBracket w11 w12 w22 p ^ 2
        * (2 * meanFit w11 w12 w22 p + (w11 - 2 * w12 + w22) * (p * (1 - p)))
        / meanFit w11 w12 w22 p ^ 2 := by
  have h1 : selStep w11 w12 w22 p = p + p * (1 - p) * selBracket w11 w12 w22 p
      / meanFit w11 w12 w22 p := by
    rw [← selStep_sub w11 w12 w22 p h]; ring
  have h2 : ∀ δ, meanFit w11 w12 w22 (p + δ) = meanFit w11 w12 w22 p
      + 2 * selBracket w11 w12 w22 p * δ + (w11 - 2 * w12 + w22) * δ ^ 2 := by
    intro δ
    simp only [meanFit, selBracket]; ring
  rw [h1, show p + p * (1 - p) * selBracket w11 w12 w22 p / meanFit w11 w12 w22 p
    = p + (p * (1 - p) * selBracket w11 w12 w22 p / meanFit w11 w12 w22 p) from rfl, h2]
  generalize meanFit w11 w12 w22 p = W at *
  generalize selBracket w11 w12 w22 p = A
  field_simp
  ring

section Order

variable [LinearOrder F] [IsStrictOrderedRing F]

/--
Source: fisher1930, ch. 2; kingman1961_selection, p. 574, eq. (4); burger2013_migration_selection,
sec. 2.2, eq. (2.13). -/
theorem meanFit_selStep_ge {w11 w12 w22 p : F} (h11 : 0 ≤ w11) (h12 : 0 ≤ w12) (h22 : 0 ≤ w22)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hW : 0 < meanFit w11 w12 w22 p) :
    meanFit w11 w12 w22 p ≤ meanFit w11 w12 w22 (selStep w11 w12 w22 p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have key : 0 ≤ 2 * meanFit w11 w12 w22 p + (w11 - 2 * w12 + w22) * (p * (1 - p)) := by
    have : 2 * meanFit w11 w12 w22 p + (w11 - 2 * w12 + w22) * (p * (1 - p))
        = w11 * (p * (2 * p + (1 - p))) + 2 * (p * (1 - p)) * w12
          + w22 * ((1 - p) * (2 * (1 - p) + p)) := by
      simp only [meanFit]; ring
    rw [this]; positivity
  have := meanFit_selStep_sub w11 w12 w22 p hW.ne'
  have h0 : 0 ≤ meanFit w11 w12 w22 (selStep w11 w12 w22 p) - meanFit w11 w12 w22 p := by
    rw [this]; positivity
  linarith

theorem meanFit_pos {w11 w12 w22 p : F} (h11 : 0 < w11) (h12 : 0 < w12) (h22 : 0 < w22)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 < meanFit w11 w12 w22 p := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have : 0 < p + (1 - p) := by linarith
  simp only [meanFit]
  rcases hp0.eq_or_lt with h | h
  · subst h; simp [h22]
  · positivity

end Order

/-- Source: crow_kimura1970, §6.2. -/
theorem polyEq_mem_Ioo_iff [LinearOrder F] [IsStrictOrderedRing F] (w11 w12 w22 : F) :
    (0 < polyEq w11 w12 w22 ∧ polyEq w11 w12 w22 < 1) ↔
      (w11 < w12 ∧ w22 < w12) ∨ (w12 < w11 ∧ w12 < w22) := by
  by_cases hD : 2 * w12 - w11 - w22 = 0
  · have : ¬ ((w11 < w12 ∧ w22 < w12) ∨ (w12 < w11 ∧ w12 < w22)) := by
      rintro (⟨a, b⟩ | ⟨a, b⟩) <;> linarith
    simp [polyEq, hD, this]
  have h1 : 1 - polyEq w11 w12 w22 = (w12 - w11) / (2 * w12 - w11 - w22) := by
    calc 1 - polyEq w11 w12 w22
        = (2 * w12 - w11 - w22) / (2 * w12 - w11 - w22) - polyEq w11 w12 w22 := by
          rw [div_self hD]
      _ = (w12 - w11) / (2 * w12 - w11 - w22) := by
          rw [polyEq, ← sub_div]; congr 1; ring
  have h2 : polyEq w11 w12 w22 < 1 ↔ 0 < 1 - polyEq w11 w12 w22 := by
    constructor <;> intro h <;> linarith
  rw [h2, h1]
  simp only [polyEq]
  rw [div_pos_iff, div_pos_iff]
  constructor
  · rintro ⟨⟨a, b⟩ | ⟨a, b⟩, ⟨c, d⟩ | ⟨c, d⟩⟩
    · left; constructor <;> linarith
    · exfalso; linarith
    · exfalso; linarith
    · right; constructor <;> linarith
  · rintro (⟨a, b⟩ | ⟨a, b⟩)
    · exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

theorem selBracket_polyEq {w11 w12 w22 : F} (hD : 2 * w12 - w11 - w22 ≠ 0) :
    selBracket w11 w12 w22 (polyEq w11 w12 w22) = 0 := by
  rw [selBracket_eq]
  simp only [polyEq]
  rw [div_mul_cancel₀ _ hD, sub_self]

theorem selStep_polyEq {w11 w12 w22 : F} (hD : 2 * w12 - w11 - w22 ≠ 0)
    (hW : meanFit w11 w12 w22 (polyEq w11 w12 w22) ≠ 0) :
    selStep w11 w12 w22 (polyEq w11 w12 w22) = polyEq w11 w12 w22 := by
  have h := selStep_sub w11 w12 w22 _ hW
  rw [selBracket_polyEq hD] at h
  simpa [sub_eq_zero] using h

theorem eq_polyEq_of_selStep_eq {w11 w12 w22 p : F} (hD : 2 * w12 - w11 - w22 ≠ 0)
    (hW : meanFit w11 w12 w22 p ≠ 0) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hfix : selStep w11 w12 w22 p = p) : p = polyEq w11 w12 w22 := by
  have h := selStep_sub w11 w12 w22 p hW
  rw [hfix, sub_self] at h
  have h1 : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have h2 : selBracket w11 w12 w22 p = 0 := by
    have := h.symm
    rw [div_eq_zero_iff] at this
    rcases this with h3 | h3
    · simpa [hp0, h1] using h3
    · exact absurd h3 hW
  rw [selBracket_eq] at h2
  simp only [polyEq]
  rw [eq_div_iff hD]
  linear_combination (-1 : F) * h2

def selStepSlope (w11 w12 w22 p : F) : F :=
  (p * w11 + (1 - p) * w22) / meanFit w11 w12 w22 p

theorem selStep_sub_polyEq {w11 w12 w22 : F} (p : F) (hD : 2 * w12 - w11 - w22 ≠ 0)
    (hW : meanFit w11 w12 w22 p ≠ 0) :
    selStep w11 w12 w22 p - polyEq w11 w12 w22
      = selStepSlope w11 w12 w22 p * (p - polyEq w11 w12 w22) := by
  simp only [selStep, selStepSlope, polyEq]
  generalize hDd : 2 * w12 - w11 - w22 = D at hD ⊢
  field_simp
  rw [← hDd]
  simp only [meanFit]
  ring

section Stability

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem selStepSlope_mem_Ioo {w11 w12 w22 p : F} (h11 : 0 < w11) (h22 : 0 < w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < selStepSlope w11 w12 w22 p ∧ selStepSlope w11 w12 w22 p < 1 := by
  obtain ⟨a, b⟩ := ho
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hW : 0 < meanFit w11 w12 w22 p := meanFit_pos h11 (by linarith) h22 hp0.le hp1.le
  have hnum : 0 < p * w11 + (1 - p) * w22 := by positivity
  refine ⟨div_pos hnum hW, ?_⟩
  rw [selStepSlope, div_lt_one hW]
  have : meanFit w11 w12 w22 p - (p * w11 + (1 - p) * w22)
      = p * (1 - p) * (2 * w12 - w11 - w22) := by
    simp only [meanFit]; ring
  have h3 : 0 < p * (1 - p) * (2 * w12 - w11 - w22) := by
    have : 0 < 2 * w12 - w11 - w22 := by linarith
    positivity
  linarith

/-- Source: fisher1922, sec. 1, p. 324; crow_kimura1970, §6.2. -/
theorem selStep_closer_of_overdominance {w11 w12 w22 p : F} (h11 : 0 < w11) (h22 : 0 < w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ polyEq w11 w12 w22) :
    |selStep w11 w12 w22 p - polyEq w11 w12 w22| < |p - polyEq w11 w12 w22| ∧
      0 < (selStep w11 w12 w22 p - polyEq w11 w12 w22) * (p - polyEq w11 w12 w22) := by
  have hD : 2 * w12 - w11 - w22 ≠ 0 := by
    have : 0 < 2 * w12 - w11 - w22 := by linarith [ho.1, ho.2]
    exact this.ne'
  have hW : meanFit w11 w12 w22 p ≠ 0 :=
    (meanFit_pos h11 (by linarith [ho.1]) h22 hp0.le hp1.le).ne'
  obtain ⟨k0, k1⟩ := selStepSlope_mem_Ioo h11 h22 ho hp0 hp1
  have hd : 0 < |p - polyEq w11 w12 w22| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hsq : 0 < (p - polyEq w11 w12 w22) * (p - polyEq w11 w12 w22) :=
    mul_self_pos.mpr (sub_ne_zero.mpr hne)
  rw [selStep_sub_polyEq p hD hW, abs_mul, abs_of_pos k0]
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

end Stability

end Rhone.Dynamics
