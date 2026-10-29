/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.LDDecay
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Bounds on `D`, Lewontin's `D'`, and `r²`

Source: lewontin1964, pp. 54–55; hill_robertson1968, p. 226; hill1981, p. 210. -/

@[expose] public section

namespace Rhone.Dynamics

namespace Gametes

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

structure IsDist (g : Gametes F) : Prop where
  x11_nonneg : 0 ≤ g.x11
  x12_nonneg : 0 ≤ g.x12
  x21_nonneg : 0 ≤ g.x21
  x22_nonneg : 0 ≤ g.x22
  total_eq : g.total = 1

/-- Source: lewontin1964, p. 55. -/
theorem D_bounds {g : Gametes F} (hg : g.IsDist) :
    max (-(g.pA * g.pB)) (-((1 - g.pA) * (1 - g.pB))) ≤ g.D ∧
      g.D ≤ min (g.pA * (1 - g.pB)) ((1 - g.pA) * g.pB) := by
  obtain ⟨h11, h12, h21, h22, ht⟩ := hg
  have e1 : 1 - g.pA = g.x21 + g.x22 := by rw [← pA'_eq ht]; rfl
  have e2 : 1 - g.pB = g.x12 + g.x22 := by rw [← pB'_eq ht]; rfl
  simp only [D, pA, pB] at *
  rw [e1, e2]
  refine ⟨max_le ?_ ?_, le_min ?_ ?_⟩
  · nlinarith [mul_nonneg h11 h11, mul_nonneg h11 h21, mul_nonneg h11 h12, mul_nonneg h12 h21,
      mul_nonneg h11 h22]
  · nlinarith [mul_nonneg h21 h21, mul_nonneg h21 h22, mul_nonneg h22 h22, mul_nonneg h12 h22,
      mul_nonneg h12 h21, mul_nonneg h11 h22, mul_nonneg h21 h12]
  · nlinarith [mul_nonneg h11 h12, mul_nonneg h12 h12, mul_nonneg h12 h22, mul_nonneg h11 h22,
      mul_nonneg h12 h21]
  · nlinarith [mul_nonneg h11 h21, mul_nonneg h21 h21, mul_nonneg h21 h22, mul_nonneg h11 h22,
      mul_nonneg h12 h21]

def dMax (pA pB D : F) : F :=
  if 0 ≤ D then min (pA * (1 - pB)) ((1 - pA) * pB) else min (pA * pB) ((1 - pA) * (1 - pB))

def lewontinD' (pA pB D : F) : F := D / dMax pA pB D

def rSq (pA pB D : F) : F := D ^ 2 / (pA * (1 - pA) * pB * (1 - pB))

theorem abs_div_le_one_of_abs_le {D M : F} (h : |D| ≤ M) : |D / M| ≤ 1 := by
  rcases ((abs_nonneg D).trans h).eq_or_lt with h0 | h0
  · have : D = 0 := by
      rw [← h0] at h; exact abs_nonpos_iff.mp h
    simp [this]
  · rw [abs_div, abs_of_pos h0, div_le_one h0]; exact h

theorem abs_lewontinD'_le_one {g : Gametes F} (hg : g.IsDist) :
    |lewontinD' g.pA g.pB g.D| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := D_bounds hg
  unfold lewontinD' dMax
  split_ifs with h
  · exact abs_div_le_one_of_abs_le (by rw [abs_of_nonneg h]; exact hhi)
  · refine abs_div_le_one_of_abs_le ?_
    rw [abs_of_neg (not_le.mp h)]
    have := max_le_iff.mp (show max (-(g.pA * g.pB)) (-((1 - g.pA) * (1 - g.pB))) ≤ g.D from hlo)
    exact le_min (by linarith [this.1]) (by linarith [this.2])

theorem lewontinD'_mul {pA pB D c : F} (hc : 0 ≤ c) :
    lewontinD' pA pB (c * D) = c * lewontinD' pA pB D := by
  rcases hc.eq_or_lt with h | h
  · subst h; simp [lewontinD']
  · have hs : 0 ≤ c * D ↔ 0 ≤ D := by
      constructor
      · intro h1; exact nonneg_of_mul_nonneg_right h1 h
      · intro h1; positivity
    simp only [lewontinD', dMax, hs]
    rw [mul_div_assoc]

theorem rSq_nonneg {g : Gametes F} (hg : g.IsDist) : 0 ≤ rSq g.pA g.pB g.D := by
  obtain ⟨h11, h12, h21, h22, ht⟩ := hg
  have e1 : 1 - g.pA = g.x21 + g.x22 := by rw [← pA'_eq ht]; rfl
  have e2 : 1 - g.pB = g.x12 + g.x22 := by rw [← pB'_eq ht]; rfl
  unfold rSq
  rw [e1, e2]
  simp only [pA, pB]
  positivity

/-- Source: hill_robertson1968, p. 228; mcvean2002, eq. (1), p. 987. -/
theorem rSq_le_one {g : Gametes F} (hg : g.IsDist) : rSq g.pA g.pB g.D ≤ 1 := by
  obtain ⟨h11, h12, h21, h22, ht⟩ := hg
  have e1 : 1 - g.pA = g.x21 + g.x22 := by rw [← pA'_eq ht]; rfl
  have e2 : 1 - g.pB = g.x12 + g.x22 := by rw [← pB'_eq ht]; rfl
  have key : g.pA * (1 - g.pA) * g.pB * (1 - g.pB) - g.D ^ 2
      = g.x11 ^ 2 * g.x12 * g.x21 + g.x11 ^ 2 * g.x12 * g.x22 + g.x11 ^ 2 * g.x21 * g.x22
        + g.x11 * g.x12 ^ 2 * g.x21 + g.x11 * g.x12 ^ 2 * g.x22 + g.x11 * g.x12 * g.x21 ^ 2
        + 4 * g.x11 * g.x12 * g.x21 * g.x22 + g.x11 * g.x12 * g.x22 ^ 2
        + g.x11 * g.x21 ^ 2 * g.x22 + g.x11 * g.x21 * g.x22 ^ 2 + g.x12 ^ 2 * g.x21 * g.x22
        + g.x12 * g.x21 ^ 2 * g.x22 + g.x12 * g.x21 * g.x22 ^ 2 := by
    rw [e1, e2]; simp only [pA, pB, D]; ring
  have hnn : 0 ≤ g.pA * (1 - g.pA) * g.pB * (1 - g.pB) - g.D ^ 2 := by
    rw [key]; positivity
  unfold rSq
  rcases (show 0 ≤ g.pA * (1 - g.pA) * g.pB * (1 - g.pB) by
      rw [e1, e2]; simp only [pA, pB]; positivity).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · rw [div_le_one h0]; linarith

section Iterate

variable {g : Gametes F} {r : F}

theorem lewontinD'_iterate (hr1 : r ≤ 1) (h : g.total = 1) (t : ℕ) :
    lewontinD' g.pA g.pB ((recombine r)^[t] g).D
      = (1 - r) ^ t * lewontinD' g.pA g.pB g.D := by
  rw [D_iterate r h t]
  exact lewontinD'_mul (pow_nonneg (sub_nonneg.mpr hr1) t)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem rSq_iterate (h : g.total = 1) (t : ℕ) :
    rSq g.pA g.pB ((recombine r)^[t] g).D = (1 - r) ^ (2 * t) * rSq g.pA g.pB g.D := by
  rw [D_iterate r h t]
  simp only [rSq, pow_mul', mul_pow, mul_div_assoc]

end Iterate

end Gametes

end Rhone.Dynamics
