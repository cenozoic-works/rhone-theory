/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisher
public import Mathlib.Tactic.Linarith

/-!
# Moran chain on counts, with constant selection

Source: moran1958; durrett2008, sec. 1.5; ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

noncomputable def moranUp (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  r * i * ((N : ℝ) - i) / (N * (r * i + ((N : ℝ) - i)))

noncomputable def moranDown (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  (i : ℝ) * ((N : ℝ) - i) / (N * (r * i + ((N : ℝ) - i)))

noncomputable def moranRow (N : ℕ) (r : ℝ) (i j : ℕ) : ℝ :=
  (if j = i then 1 - moranUp N r i - moranDown N r i else 0)
    + (if j = i + 1 then moranUp N r i else 0)
    + (if i = j + 1 then moranDown N r i else 0)

noncomputable def moran (N : ℕ) (r : ℝ) : CountKernel N := fun i j => moranRow N r i j

theorem moran_apply (N : ℕ) (r : ℝ) (i j : Fin (N + 1)) : moran N r i j = moranRow N r i j := rfl

section Probabilities

variable {N i : ℕ} {r : ℝ}

private theorem sub_nonneg_of_count_le (hi : i ≤ N) : (0 : ℝ) ≤ (N : ℝ) - i := by
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  linarith

theorem moranUp_nonneg (hr : 0 < r) (hi : i ≤ N) : 0 ≤ moranUp N r i := by
  have := sub_nonneg_of_count_le hi
  unfold moranUp
  positivity

theorem moranDown_nonneg (hr : 0 < r) (hi : i ≤ N) : 0 ≤ moranDown N r i := by
  have := sub_nonneg_of_count_le hi
  unfold moranDown
  positivity

theorem moranUp_self (r : ℝ) (N : ℕ) : moranUp N r N = 0 := by simp [moranUp]

theorem moranDown_zero (r : ℝ) (N : ℕ) : moranDown N r 0 = 0 := by simp [moranDown]

theorem moranUp_zero (r : ℝ) (N : ℕ) : moranUp N r 0 = 0 := by simp [moranUp]

theorem moranDown_self (r : ℝ) (N : ℕ) : moranDown N r N = 0 := by simp [moranDown]

theorem moranUp_add_moranDown_le (hr : 0 < r) (hi : i ≤ N) :
    moranUp N r i + moranDown N r i ≤ 1 := by
  have h0 := sub_nonneg_of_count_le hi
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [moranUp, moranDown]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < (N : ℝ) * (r * i + ((N : ℝ) - i)) := by
    have : 0 < r * i + ((N : ℝ) - i) := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hN'
      · have : (0 : ℝ) < i := by exact_mod_cast hi0
        positivity
    positivity
  unfold moranUp moranDown
  rw [← add_div, div_le_one hd]
  nlinarith [sq_nonneg ((N : ℝ) - i), mul_nonneg hr.le (sq_nonneg (i : ℝ))]

theorem moranUp_one (N i : ℕ) : moranUp N 1 i = (i : ℝ) * ((N : ℝ) - i) / (N : ℝ) ^ 2 := by
  unfold moranUp
  rw [one_mul, add_sub_cancel, sq]

theorem moranDown_one (N i : ℕ) : moranDown N 1 i = (i : ℝ) * ((N : ℝ) - i) / (N : ℝ) ^ 2 := by
  unfold moranDown
  rw [one_mul, add_sub_cancel, sq]

theorem moranUp_eq_mul_moranDown (N : ℕ) (r : ℝ) (i : ℕ) :
    moranUp N r i = r * moranDown N r i := by
  unfold moranUp moranDown
  ring

end Probabilities

section Expectation

variable {N : ℕ} {r : ℝ}

theorem sum_moranRow_mul (f : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    ∑ j ∈ range (N + 1), moranRow N r i j * f j =
      (1 - moranUp N r i - moranDown N r i) * f i + moranUp N r i * f (i + 1)
        + moranDown N r i * f (i - 1) := by
  simp only [moranRow, add_mul, sum_add_distrib, ite_mul, zero_mul]
  rw [sum_ite_eq' (range (N + 1)) i, sum_ite_eq' (range (N + 1)) (i + 1)]
  have h1 : i ∈ range (N + 1) := mem_range.mpr (by omega)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [moranUp, moranDown]
    · simp [moranDown_zero, moranUp_zero]
  · have h3 : ∑ j ∈ range (N + 1), (if i = j + 1 then moranDown N r i * f j else 0) =
        moranDown N r i * f (i - 1) := by
      rw [sum_eq_single (i - 1)]
      · simp [Nat.sub_add_cancel hi0]
      · intro b _ hb
        have : ¬ i = b + 1 := by omega
        simp [this]
      · intro h
        exact absurd (mem_range.mpr (by omega)) h
    rw [h3]
    rcases Nat.lt_or_ge i N with hlt | hge
    · have : i + 1 ∈ range (N + 1) := mem_range.mpr (by omega)
      simp [h1, this]
    · have hiN : i = N := by omega
      subst hiN
      simp [moranUp_self]

theorem moran_isStochastic (hr : 0 < r) (N : ℕ) : (moran N r).IsStochastic := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
    have h1 := moranUp_nonneg hr hi
    have h2 := moranDown_nonneg hr hi
    have h3 := moranUp_add_moranDown_le hr hi
    simp only [moran_apply, moranRow]
    split_ifs <;> linarith
  · have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
    simp only [moran_apply]
    have := sum_moranRow_mul (r := r) (fun _ => (1 : ℝ)) hi
    simp only [mul_one] at this
    rw [sum_fin_eq_range (fun j => moranRow N r i j), this]
    ring

theorem moran_expect (f : ℕ → ℝ) (i : Fin (N + 1)) :
    (moran N r).expect (fun j => f j) i =
      f i + moranUp N r i * (f (i + 1) - f i) + moranDown N r i * (f (i - 1) - f i) := by
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
  simp only [CountKernel.expect, moran_apply]
  rw [sum_fin_eq_range (fun j => moranRow N r i j * f j), sum_moranRow_mul f hi]
  ring

theorem moran_expect_id_neutral (N : ℕ) (i : Fin (N + 1)) :
    (moran N 1).expect (fun j => (j : ℝ)) i = i := by
  rw [moran_expect (fun n => (n : ℝ)) i, moranUp_one, moranDown_one]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0]
  · have : (((i : ℕ) - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simp only [Nat.cast_add, this]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · have : (i : ℕ) = 0 := by omega
      omega
    · have : (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring

end Expectation

end Rhone.MarkovChain
