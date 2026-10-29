/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Data
public import Rhone.Algebra.GaloisDegreeSeven.AllRealBasic
public import Rhone.Algebra.GaloisDegreeSeven.Data
public import Mathlib.Topology.Order.IntermediateValue

/-! # Finding 72 as a theorem: on the parameter domain every `ρ`-pole is real and negative -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial LinearAlgebra.Tridiag

theorem E22_val (θA θB σ x : ℝ) (hσ : θA * 2 + θB * 2 = σ) :
    (Epoly ℝ 2 2 θA θB).eval x =
      (2 * σ + 8) * x ^ 2
      + (3 * σ ^ 2 + 38 * σ + 104) * x
      + (σ ^ 3 + 20 * σ ^ 2 + 108 * σ + 144) := by
  rw [eval_Epoly, Rhone.Algebra.Galois.E_two_two_s θA θB x σ hσ]

theorem E22_sep0 (θA θB σ : ℝ) (hσ : θA * 2 + θB * 2 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 2 2 θA θB).eval (0 : ℝ) > 0 := by
  have hN : (0 : ℝ) <
      σ ^ 3 + 20 * σ ^ 2 + 108 * σ + 144 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3]
  have hEq : (Epoly ℝ 2 2 θA θB).eval (0 : ℝ) =
      σ ^ 3 + 20 * σ ^ 2 + 108 * σ + 144 := by
    rw [E22_val θA θB σ (0 : ℝ) hσ]
    ring
  linarith [hN, hEq]

theorem E22_sep1 (θA θB σ : ℝ) (hσ : θA * 2 + θB * 2 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 2 2 θA θB).eval (-(2 * σ + 5) / 3) < 0 := by
  have hN : (0 : ℝ) <
      σ ^ 3 + 21 * σ ^ 2 + 12 * σ + 64 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3]
  have hEq : (9 : ℝ) * (Epoly ℝ 2 2 θA θB).eval (-(2 * σ + 5) / 3) =
      -σ ^ 3 - 21 * σ ^ 2 - 12 * σ - 64 := by
    rw [E22_val θA θB σ (-(2 * σ + 5) / 3) hσ]
    ring
  linarith [hN, hEq]

theorem E22_sep2 (θA θB σ : ℝ) (hσ : θA * 2 + θB * 2 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 2 2 θA θB).eval (-(σ + 12)) > 0 := by
  have hN : (0 : ℝ) <
      2 * σ ^ 2 + 28 * σ + 48 := by
    linarith [h0, pow_nonneg h0 2]
  have hEq : (Epoly ℝ 2 2 θA θB).eval (-(σ + 12)) =
      2 * σ ^ 2 + 28 * σ + 48 := by
    rw [E22_val θA θB σ (-(σ + 12)) hσ]
    ring
  linarith [hN, hEq]

theorem E22_ord0 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 5) / 3) < (0 : ℝ) := by
  linarith

theorem E22_ord1 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(σ + 12)) < (-(2 * σ + 5) / 3) := by
  linarith

theorem E22_roots (θA θB σ : ℝ) (hσ : θA * 2 + θB * 2 = σ) (h0 : 0 ≤ σ) :
    ∃ x1 x2 : ℝ,
      x1 < x2 ∧ (Epoly ℝ 2 2 θA θB).eval x1 = 0 ∧ (Epoly ℝ 2 2 θA θB).eval x2 = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => (Epoly ℝ 2 2 θA θB).eval x) s :=
    fun _ => (Epoly ℝ 2 2 θA θB).continuousOn
  obtain ⟨y0, hy0, hr0⟩ := intermediate_value_Ioo
    (le_of_lt (E22_ord0 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E22_sep1 θA θB σ hσ h0, E22_sep0 θA θB σ hσ h0⟩)
  obtain ⟨y1, hy1, hr1⟩ := intermediate_value_Ioo'
    (le_of_lt (E22_ord1 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E22_sep1 θA θB σ hσ h0, E22_sep2 θA θB σ hσ h0⟩)
  rw [Set.mem_Ioo] at hy0 hy1
  exact ⟨ y1, y0, lt_trans hy1.2 hy0.1, hr1, hr0⟩

theorem E22_splits_and_card (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 2 2 θA θB).roots = 2 ∧ (Epoly ℝ 2 2 θA θB).Splits := by
  have h0 : (0 : ℝ) ≤ θA * 2 + θB * 2 := by linarith
  obtain ⟨ x1, x2, o0, r0, r1⟩ := E22_roots θA θB _ rfl h0
  have hdeg : (Epoly ℝ 2 2 θA θB).natDegree = 2 := by
    have h := natDegree_Epoly (F := ℝ) (i := 2) (j := 2) (by norm_num) (by norm_num) hA hB
    simpa using h
  have hne : (Epoly ℝ 2 2 θA θB) ≠ 0 := Epoly_ne_zero (by norm_num) (by norm_num) hA hB
  have hcard : ({x1, x2} : Finset ℝ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [o0.ne])]
    rw [Finset.card_singleton]
  obtain ⟨hcards, hsplits⟩ := card_roots_eq_of_card_le hne
    ({x1, x2} : Finset ℝ) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    (le_of_eq (by rw [hdeg, hcard]))
  exact ⟨by rw [hcards, hdeg], hsplits⟩

theorem E22_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (Epoly ℝ 2 2 θA θB).Splits := (E22_splits_and_card θA θB hA hB).2

theorem card_roots_E22 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 2 2 θA θB).roots = 2 := (E22_splits_and_card θA θB hA hB).1

theorem roots_neg_E22 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (Epoly ℝ 2 2 θA θB).roots) : x < 0 := by
  rw [mem_roots (Epoly_ne_zero (by norm_num) (by norm_num) hA hB)] at hx
  exact Epoly_root_neg (by norm_num) (by norm_num) hA hB hx

theorem E33_val (θA θB σ x : ℝ) (hσ : θA * 3 + θB * 3 = σ) :
    (Epoly ℝ 3 3 θA θB).eval x =
      (6 * σ + 72) * x ^ 3
      + (11 * σ ^ 2 + 354 * σ + 2664) * x ^ 2
      + (6 * σ ^ 3 + 306 * σ ^ 2 + 4812 * σ + 23184) * x
      + (σ ^ 4 + 68 * σ ^ 3 + 1572 * σ ^ 2 + 14400 * σ + 43200) := by
  rw [eval_Epoly, Rhone.Algebra.Galois.E_three_three_s θA θB x σ hσ]

theorem E33_sep0 (θA θB σ : ℝ) (hσ : θA * 3 + θB * 3 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 3 3 θA θB).eval (0 : ℝ) > 0 := by
  have hN : (0 : ℝ) <
      σ ^ 4 + 68 * σ ^ 3 + 1572 * σ ^ 2 + 14400 * σ + 43200 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]
  have hEq : (Epoly ℝ 3 3 θA θB).eval (0 : ℝ) =
      σ ^ 4 + 68 * σ ^ 3 + 1572 * σ ^ 2 + 14400 * σ + 43200 := by
    rw [E33_val θA θB σ (0 : ℝ) hσ]
    ring
  linarith [hN, hEq]

theorem E33_sep1 (θA θB σ : ℝ) (hσ : θA * 3 + θB * 3 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 3 3 θA θB).eval (-(2 * σ + 13) / 5) < 0 := by
  have hN : (0 : ℝ) <
      3 * σ ^ 4 + 322 * σ ^ 3 + 6251 * σ ^ 2 + 17520 * σ + 41904 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]
  have hEq : (125 : ℝ) * (Epoly ℝ 3 3 θA θB).eval (-(2 * σ + 13) / 5) =
      -3 * σ ^ 4 - 322 * σ ^ 3 - 6251 * σ ^ 2 - 17520 * σ - 41904 := by
    rw [E33_val θA θB σ (-(2 * σ + 13) / 5) hσ]
    ring
  linarith [hN, hEq]

theorem E33_sep2 (θA θB σ : ℝ) (hσ : θA * 3 + θB * 3 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 3 3 θA θB).eval (-(2 * σ + 28) / 3) > 0 := by
  have hN : (0 : ℝ) <
      3 * σ ^ 4 + 168 * σ ^ 3 + 3084 * σ ^ 2 + 16176 * σ + 9216 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]
  have hEq : (27 : ℝ) * (Epoly ℝ 3 3 θA θB).eval (-(2 * σ + 28) / 3) =
      3 * σ ^ 4 + 168 * σ ^ 3 + 3084 * σ ^ 2 + 16176 * σ + 9216 := by
    rw [E33_val θA θB σ (-(2 * σ + 28) / 3) hσ]
    ring
  linarith [hN, hEq]

theorem E33_sep3 (θA θB σ : ℝ) (hσ : θA * 3 + θB * 3 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 3 3 θA θB).eval (-(σ + 26)) < 0 := by
  have hN : (0 : ℝ) <
      8 * σ ^ 3 + 472 * σ ^ 2 + 7536 * σ + 24192 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3]
  have hEq : (Epoly ℝ 3 3 θA θB).eval (-(σ + 26)) =
      -8 * σ ^ 3 - 472 * σ ^ 2 - 7536 * σ - 24192 := by
    rw [E33_val θA θB σ (-(σ + 26)) hσ]
    ring
  linarith [hN, hEq]

theorem E33_ord0 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 13) / 5) < (0 : ℝ) := by
  linarith

theorem E33_ord1 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 28) / 3) < (-(2 * σ + 13) / 5) := by
  linarith

theorem E33_ord2 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(σ + 26)) < (-(2 * σ + 28) / 3) := by
  linarith

theorem E33_roots (θA θB σ : ℝ) (hσ : θA * 3 + θB * 3 = σ) (h0 : 0 ≤ σ) :
    ∃ x1 x2 x3 : ℝ,
      x1 < x2 ∧ x2 < x3 ∧ (Epoly ℝ 3 3 θA θB).eval x1 = 0 ∧ (Epoly ℝ 3 3 θA θB).eval x2 = 0 ∧
        (Epoly ℝ 3 3 θA θB).eval x3 = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => (Epoly ℝ 3 3 θA θB).eval x) s :=
    fun _ => (Epoly ℝ 3 3 θA θB).continuousOn
  obtain ⟨y0, hy0, hr0⟩ := intermediate_value_Ioo
    (le_of_lt (E33_ord0 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E33_sep1 θA θB σ hσ h0, E33_sep0 θA θB σ hσ h0⟩)
  obtain ⟨y1, hy1, hr1⟩ := intermediate_value_Ioo'
    (le_of_lt (E33_ord1 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E33_sep1 θA θB σ hσ h0, E33_sep2 θA θB σ hσ h0⟩)
  obtain ⟨y2, hy2, hr2⟩ := intermediate_value_Ioo
    (le_of_lt (E33_ord2 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E33_sep3 θA θB σ hσ h0, E33_sep2 θA θB σ hσ h0⟩)
  rw [Set.mem_Ioo] at hy0 hy1 hy2
  exact ⟨ y2, y1, y0, lt_trans hy2.2 hy1.1, lt_trans hy1.2 hy0.1, hr2, hr1, hr0⟩

theorem E33_splits_and_card (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 3 3 θA θB).roots = 3 ∧ (Epoly ℝ 3 3 θA θB).Splits := by
  have h0 : (0 : ℝ) ≤ θA * 3 + θB * 3 := by linarith
  obtain ⟨ x1, x2, x3, o0, o1, r0, r1, r2⟩ := E33_roots θA θB _ rfl h0
  have hdeg : (Epoly ℝ 3 3 θA θB).natDegree = 3 := by
    have h := natDegree_Epoly (F := ℝ) (i := 3) (j := 3) (by norm_num) (by norm_num) hA hB
    simpa using h
  have hne : (Epoly ℝ 3 3 θA θB) ≠ 0 := Epoly_ne_zero (by norm_num) (by norm_num) hA hB
  have hcard : ({x1, x2, x3} : Finset ℝ).card = 3 := by
    have h02 : x1 < x3 := by linarith
    rw [Finset.card_insert_of_notMem (by simp [o0.ne, h02.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o1.ne])]
    rw [Finset.card_singleton]
  obtain ⟨hcards, hsplits⟩ := card_roots_eq_of_card_le hne
    ({x1, x2, x3} : Finset ℝ) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    (le_of_eq (by rw [hdeg, hcard]))
  exact ⟨by rw [hcards, hdeg], hsplits⟩

theorem E33_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (Epoly ℝ 3 3 θA θB).Splits := (E33_splits_and_card θA θB hA hB).2

theorem card_roots_E33 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 3 3 θA θB).roots = 3 := (E33_splits_and_card θA θB hA hB).1

theorem roots_neg_E33 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (Epoly ℝ 3 3 θA θB).roots) : x < 0 := by
  rw [mem_roots (Epoly_ne_zero (by norm_num) (by norm_num) hA hB)] at hx
  exact Epoly_root_neg (by norm_num) (by norm_num) hA hB hx

theorem E55_val (θA θB σ x : ℝ) (hσ : θA * 5 + θB * 5 = σ) :
    (Epoly ℝ 5 5 θA θB).eval x =
      (120 * σ + 4800) * x ^ 5
      + (274 * σ ^ 2 + 26720 * σ + 630400) * x ^ 4
      + (225 * σ ^ 3 + 34658 * σ ^ 2 + 1725640 * σ + 27780800) * x ^ 3
      + (85 * σ ^ 4 + 17730 * σ ^ 3 + 1339728 * σ ^ 2 + 43408640 * σ + 508172800) * x ^ 2
      + (15 * σ ^ 5 + 3910 * σ ^ 4 + 391956 * σ ^ 3 + 18842552 * σ ^ 2 + 433277280 * σ
          + 3801888000) * x
      + (σ ^ 6 + 310 * σ ^ 5 + 38308 * σ ^ 4 + 2407464 * σ ^ 3 + 80868960 * σ ^ 2
          + 1371686400 * σ + 9144576000) := by
  rw [eval_Epoly, Rhone.Algebra.Galois.E_five_five_s θA θB x σ hσ]

theorem E55_sep0 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (0 : ℝ) > 0 := by
  have hN : (0 : ℝ) <
      σ ^ 6 + 310 * σ ^ 5 + 38308 * σ ^ 4 + 2407464 * σ ^ 3 + 80868960 * σ ^ 2 + 1371686400 * σ
        + 9144576000 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6]
  have hEq : (Epoly ℝ 5 5 θA θB).eval (0 : ℝ) =
      σ ^ 6 + 310 * σ ^ 5 + 38308 * σ ^ 4 + 2407464 * σ ^ 3 + 80868960 * σ ^ 2 + 1371686400 * σ
        + 9144576000 := by
    rw [E55_val θA θB σ (0 : ℝ) hσ]
    ring
  linarith [hN, hEq]

theorem E55_sep1 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 42) / 9) < 0 := by
  have hN : (0 : ℝ) <
      105 * σ ^ 6 + 63060 * σ ^ 5 + 11928708 * σ ^ 4 + 920335392 * σ ^ 3 + 30581509824 * σ ^ 2
        + 454233484800 * σ + 3878867865600 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6]
  have hEq : (59049 : ℝ) * (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 42) / 9) =
      -105 * σ ^ 6 - 63060 * σ ^ 5 - 11928708 * σ ^ 4 - 920335392 * σ ^ 3 - 30581509824 * σ ^ 2
        - 454233484800 * σ - 3878867865600 := by
    rw [E55_val θA θB σ (-(2 * σ + 42) / 9) hσ]
    ring
  linarith [hN, hEq]

theorem E55_sep2 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 71) / 7) > 0 := by
  have hN : (0 : ℝ) <
      45 * σ ^ 6 + 18765 * σ ^ 5 + 2454343 * σ ^ 4 + 131416391 * σ ^ 3 + 2518328568 * σ ^ 2
        + 10010811200 * σ + 510749171200 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6]
  have hEq : (16807 : ℝ) * (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 71) / 7) =
      45 * σ ^ 6 + 18765 * σ ^ 5 + 2454343 * σ ^ 4 + 131416391 * σ ^ 3 + 2518328568 * σ ^ 2
        + 10010811200 * σ + 510749171200 := by
    rw [E55_val θA θB σ (-(2 * σ + 71) / 7) hσ]
    ring
  linarith [hN, hEq]

theorem E55_sep3 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 96) / 5) < 0 := by
  have hN : (0 : ℝ) <
      45 * σ ^ 6 + 14310 * σ ^ 5 + 1791220 * σ ^ 4 + 109296040 * σ ^ 3 + 3210342880 * σ ^ 2
        + 34540523520 * σ + 12114892800 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6]
  have hEq : (3125 : ℝ) * (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 96) / 5) =
      -45 * σ ^ 6 - 14310 * σ ^ 5 - 1791220 * σ ^ 4 - 109296040 * σ ^ 3 - 3210342880 * σ ^ 2
        - 34540523520 * σ - 12114892800 := by
    rw [E55_val θA θB σ (-(2 * σ + 96) / 5) hσ]
    ring
  linarith [hN, hEq]

theorem E55_sep4 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 103) / 3) > 0 := by
  have hN : (0 : ℝ) <
      105 * σ ^ 6 + 28341 * σ ^ 5 + 3139131 * σ ^ 4 + 178481991 * σ ^ 3 + 5224633056 * σ ^ 2
        + 64514578560 * σ + 65120140800 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6]
  have hEq : (243 : ℝ) * (Epoly ℝ 5 5 θA θB).eval (-(2 * σ + 103) / 3) =
      105 * σ ^ 6 + 28341 * σ ^ 5 + 3139131 * σ ^ 4 + 178481991 * σ ^ 3 + 5224633056 * σ ^ 2
        + 64514578560 * σ + 65120140800 := by
    rw [E55_val θA θB σ (-(2 * σ + 103) / 3) hσ]
    ring
  linarith [hN, hEq]

theorem E55_sep5 (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 5 5 θA θB).eval (-(σ + 64)) < 0 := by
  have hN : (0 : ℝ) <
      144 * σ ^ 5 + 37992 * σ ^ 4 + 3785808 * σ ^ 3 + 171915008 * σ ^ 2 + 3241363200 * σ
        + 12874291200 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5]
  have hEq : (Epoly ℝ 5 5 θA θB).eval (-(σ + 64)) =
      -144 * σ ^ 5 - 37992 * σ ^ 4 - 3785808 * σ ^ 3 - 171915008 * σ ^ 2 - 3241363200 * σ
        - 12874291200 := by
    rw [E55_val θA θB σ (-(σ + 64)) hσ]
    ring
  linarith [hN, hEq]

theorem E55_ord0 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 42) / 9) < (0 : ℝ) := by
  linarith

theorem E55_ord1 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 71) / 7) < (-(2 * σ + 42) / 9) := by
  linarith

theorem E55_ord2 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 96) / 5) < (-(2 * σ + 71) / 7) := by
  linarith

theorem E55_ord3 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 103) / 3) < (-(2 * σ + 96) / 5) := by
  linarith

theorem E55_ord4 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(σ + 64)) < (-(2 * σ + 103) / 3) := by
  linarith

theorem E55_roots (θA θB σ : ℝ) (hσ : θA * 5 + θB * 5 = σ) (h0 : 0 ≤ σ) :
    ∃ x1 x2 x3 x4 x5 : ℝ,
      x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ (Epoly ℝ 5 5 θA θB).eval x1 = 0 ∧
        (Epoly ℝ 5 5 θA θB).eval x2 = 0 ∧ (Epoly ℝ 5 5 θA θB).eval x3 = 0 ∧
        (Epoly ℝ 5 5 θA θB).eval x4 = 0 ∧ (Epoly ℝ 5 5 θA θB).eval x5 = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => (Epoly ℝ 5 5 θA θB).eval x) s :=
    fun _ => (Epoly ℝ 5 5 θA θB).continuousOn
  obtain ⟨y0, hy0, hr0⟩ := intermediate_value_Ioo
    (le_of_lt (E55_ord0 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E55_sep1 θA θB σ hσ h0, E55_sep0 θA θB σ hσ h0⟩)
  obtain ⟨y1, hy1, hr1⟩ := intermediate_value_Ioo'
    (le_of_lt (E55_ord1 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E55_sep1 θA θB σ hσ h0, E55_sep2 θA θB σ hσ h0⟩)
  obtain ⟨y2, hy2, hr2⟩ := intermediate_value_Ioo
    (le_of_lt (E55_ord2 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E55_sep3 θA θB σ hσ h0, E55_sep2 θA θB σ hσ h0⟩)
  obtain ⟨y3, hy3, hr3⟩ := intermediate_value_Ioo'
    (le_of_lt (E55_ord3 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E55_sep3 θA θB σ hσ h0, E55_sep4 θA θB σ hσ h0⟩)
  obtain ⟨y4, hy4, hr4⟩ := intermediate_value_Ioo
    (le_of_lt (E55_ord4 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E55_sep5 θA θB σ hσ h0, E55_sep4 θA θB σ hσ h0⟩)
  rw [Set.mem_Ioo] at hy0 hy1 hy2 hy3 hy4
  exact ⟨ y4, y3, y2, y1, y0, lt_trans hy4.2 hy3.1, lt_trans hy3.2 hy2.1, lt_trans hy2.2 hy1.1,
    lt_trans hy1.2 hy0.1, hr4, hr3, hr2, hr1, hr0⟩

theorem E55_splits_and_card (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 5 5 θA θB).roots = 5 ∧ (Epoly ℝ 5 5 θA θB).Splits := by
  have h0 : (0 : ℝ) ≤ θA * 5 + θB * 5 := by linarith
  obtain ⟨ x1, x2, x3, x4, x5, o0, o1, o2, o3, r0, r1, r2, r3, r4⟩ := E55_roots θA θB _ rfl h0
  have hdeg : (Epoly ℝ 5 5 θA θB).natDegree = 5 := by
    have h := natDegree_Epoly (F := ℝ) (i := 5) (j := 5) (by norm_num) (by norm_num) hA hB
    simpa using h
  have hne : (Epoly ℝ 5 5 θA θB) ≠ 0 := Epoly_ne_zero (by norm_num) (by norm_num) hA hB
  have hcard : ({x1, x2, x3, x4, x5} : Finset ℝ).card = 5 := by
    have h02 : x1 < x3 := by linarith
    have h03 : x1 < x4 := by linarith
    have h04 : x1 < x5 := by linarith
    have h13 : x2 < x4 := by linarith
    have h14 : x2 < x5 := by linarith
    have h24 : x3 < x5 := by linarith
    rw [Finset.card_insert_of_notMem (by simp [o0.ne, h02.ne, h03.ne, h04.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o1.ne, h13.ne, h14.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o2.ne, h24.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o3.ne])]
    rw [Finset.card_singleton]
  obtain ⟨hcards, hsplits⟩ := card_roots_eq_of_card_le hne
    ({x1, x2, x3, x4, x5} : Finset ℝ) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)
    (le_of_eq (by rw [hdeg, hcard]))
  exact ⟨by rw [hcards, hdeg], hsplits⟩

theorem E55_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (Epoly ℝ 5 5 θA θB).Splits := (E55_splits_and_card θA θB hA hB).2

theorem card_roots_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 5 5 θA θB).roots = 5 := (E55_splits_and_card θA θB hA hB).1

theorem roots_neg_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (Epoly ℝ 5 5 θA θB).roots) : x < 0 := by
  rw [mem_roots (Epoly_ne_zero (by norm_num) (by norm_num) hA hB)] at hx
  exact Epoly_root_neg (by norm_num) (by norm_num) hA hB hx

theorem E77_val (θA θB σ x : ℝ) (hσ : θA * 7 + θB * 7 = σ) :
    (Epoly ℝ 7 7 θA θB).eval x =
      (5040 * σ + 423360) * x ^ 7
      + (13068 * σ ^ 2 + 2583504 * σ + 124806528) * x ^ 6
      + (13132 * σ ^ 3 + 4086792 * σ ^ 2 + 415976400 * σ + 13853439936) * x ^ 5
      + (6769 * σ ^ 4 + 2863404 * σ ^ 3 + 445291452 * σ ^ 2 + 30167634672 * σ
          + 751179840768) * x ^ 4
      + (1960 * σ ^ 5 + 1043196 * σ ^ 4 + 217330464 * σ ^ 3 + 22141116144 * σ ^ 2
          + 1102464381312 * σ + 21451318608384) * x ^ 3
      + (322 * σ ^ 6 + 205548 * σ ^ 5 + 53389716 * σ ^ 4 + 7216583840 * σ ^ 3
          + 534906581328 * σ ^ 2 + 20595604776768 * σ + 321509264380416) * x ^ 2
      + (28 * σ ^ 7 + 20748 * σ ^ 6 + 6421128 * σ ^ 5 + 1074706400 * σ ^ 4
          + 104940412512 * σ ^ 3 + 5971222911168 * σ ^ 2 + 183108462485760 * σ
          + 2331552477284352) * x
      + (σ ^ 8 + 840 * σ ^ 7 + 300216 * σ ^ 6 + 59549408 * σ ^ 5 + 7160537424 * σ ^ 4
          + 533762786304 * σ ^ 3 + 24054423918336 * σ ^ 2 + 598391790796800 * σ
          + 6283113803366400) := by
  rw [eval_Epoly, E_seven_seven_s θA θB x σ hσ]

theorem E77_sep0 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (0 : ℝ) > 0 := by
  have hN : (0 : ℝ) <
      σ ^ 8 + 840 * σ ^ 7 + 300216 * σ ^ 6 + 59549408 * σ ^ 5 + 7160537424 * σ ^ 4
        + 533762786304 * σ ^ 3 + 24054423918336 * σ ^ 2 + 598391790796800 * σ
        + 6283113803366400 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (Epoly ℝ 7 7 θA θB).eval (0 : ℝ) =
      σ ^ 8 + 840 * σ ^ 7 + 300216 * σ ^ 6 + 59549408 * σ ^ 5 + 7160537424 * σ ^ 4
        + 533762786304 * σ ^ 3 + 24054423918336 * σ ^ 2 + 598391790796800 * σ
        + 6283113803366400 := by
    rw [E77_val θA θB σ (0 : ℝ) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep1 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 86) / 13) < 0 := by
  have hN : (0 : ℝ) <
      10395 * σ ^ 8 + 17879640 * σ ^ 7 + 11330789992 * σ ^ 6 + 3489394104288 * σ ^ 5
        + 570113368358256 * σ ^ 4 + 50020967444790528 * σ ^ 3 + 2259311130546170112 * σ ^ 2
        + 48435878276233426944 * σ + 483408228021407797248 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (62748517 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 86) / 13) =
      -10395 * σ ^ 8 - 17879640 * σ ^ 7 - 11330789992 * σ ^ 6 - 3489394104288 * σ ^ 5
        - 570113368358256 * σ ^ 4 - 50020967444790528 * σ ^ 3 - 2259311130546170112 * σ ^ 2
        - 48435878276233426944 * σ - 483408228021407797248 := by
    rw [E77_val θA θB σ (-(2 * σ + 86) / 13) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep2 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 130) / 11) > 0 := by
  have hN : (0 : ℝ) <
      2835 * σ ^ 8 + 3870504 * σ ^ 7 + 1869840936 * σ ^ 6 + 426024212256 * σ ^ 5
        + 48938707680624 * σ ^ 4 + 2677940553408768 * σ ^ 3 + 71212623320897280 * σ ^ 2
        + 4083168195170942976 * σ + 220397428499810365440 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (19487171 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 130) / 11) =
      2835 * σ ^ 8 + 3870504 * σ ^ 7 + 1869840936 * σ ^ 6 + 426024212256 * σ ^ 5
        + 48938707680624 * σ ^ 4 + 2677940553408768 * σ ^ 3 + 71212623320897280 * σ ^ 2
        + 4083168195170942976 * σ + 220397428499810365440 := by
    rw [E77_val θA θB σ (-(2 * σ + 130) / 11) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep3 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 172) / 9) < 0 := by
  have hN : (0 : ℝ) <
      1575 * σ ^ 8 + 1724400 * σ ^ 7 + 719911800 * σ ^ 6 + 152574500160 * σ ^ 5
        + 17416341677808 * σ ^ 4 + 988002167846400 * σ ^ 3 + 19183195876025088 * σ ^ 2
        + 141420284836927488 * σ + 30425766186080305152 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (4782969 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 172) / 9) =
      -1575 * σ ^ 8 - 1724400 * σ ^ 7 - 719911800 * σ ^ 6 - 152574500160 * σ ^ 5
        - 17416341677808 * σ ^ 4 - 988002167846400 * σ ^ 3 - 19183195876025088 * σ ^ 2
        - 141420284836927488 * σ - 30425766186080305152 := by
    rw [E77_val θA θB σ (-(2 * σ + 172) / 9) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep4 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 207) / 7) > 0 := by
  have hN : (0 : ℝ) <
      1575 * σ ^ 8 + 1480500 * σ ^ 7 + 592502778 * σ ^ 6 + 130822893684 * σ ^ 5
        + 17211316236471 * σ ^ 4 + 1348411523552352 * σ ^ 3 + 58653437886100512 * σ ^ 2
        + 1192906423541629440 * σ + 8956022137645443840 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (823543 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 207) / 7) =
      1575 * σ ^ 8 + 1480500 * σ ^ 7 + 592502778 * σ ^ 6 + 130822893684 * σ ^ 5
        + 17211316236471 * σ ^ 4 + 1348411523552352 * σ ^ 3 + 58653437886100512 * σ ^ 2
        + 1192906423541629440 * σ + 8956022137645443840 := by
    rw [E77_val θA θB σ (-(2 * σ + 207) / 7) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep5 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 223) / 5) < 0 := by
  have hN : (0 : ℝ) <
      2835 * σ ^ 8 + 2404620 * σ ^ 7 + 892495530 * σ ^ 6 + 187524423540 * σ ^ 5
        + 24060982236075 * σ ^ 4 + 1887818405889240 * σ ^ 3 + 84540724104196080 * σ ^ 2
        + 1737685068564049920 * σ + 4957324976713052160 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (78125 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 223) / 5) =
      -2835 * σ ^ 8 - 2404620 * σ ^ 7 - 892495530 * σ ^ 6 - 187524423540 * σ ^ 5
        - 24060982236075 * σ ^ 4 - 1887818405889240 * σ ^ 3 - 84540724104196080 * σ ^ 2
        - 1737685068564049920 * σ - 4957324976713052160 := by
    rw [E77_val θA θB σ (-(2 * σ + 223) / 5) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep6 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 203) / 3) > 0 := by
  have hN : (0 : ℝ) <
      10395 * σ ^ 8 + 7390692 * σ ^ 7 + 2266617906 * σ ^ 6 + 388693633572 * σ ^ 5
        + 40256601054507 * σ ^ 4 + 2519991064734048 * σ ^ 3 + 88589890808687520 * σ ^ 2
        + 1376112598681379328 * σ + 1483314093204975360 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7, pow_nonneg h0 8]
  have hEq : (2187 : ℝ) * (Epoly ℝ 7 7 θA θB).eval (-(2 * σ + 203) / 3) =
      10395 * σ ^ 8 + 7390692 * σ ^ 7 + 2266617906 * σ ^ 6 + 388693633572 * σ ^ 5
        + 40256601054507 * σ ^ 4 + 2519991064734048 * σ ^ 3 + 88589890808687520 * σ ^ 2
        + 1376112598681379328 * σ + 1483314093204975360 := by
    rw [E77_val θA θB σ (-(2 * σ + 203) / 3) hσ]
    ring
  linarith [hN, hEq]

theorem E77_sep7 (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ)
    (h0 : 0 ≤ σ) :
    (Epoly ℝ 7 7 θA θB).eval (-(σ + 117)) < 0 := by
  have hN : (0 : ℝ) <
      5040 * σ ^ 7 + 3527316 * σ ^ 6 + 1031242540 * σ ^ 5 + 161769520119 * σ ^ 4
        + 14471205382512 * σ ^ 3 + 714901006709856 * σ ^ 2 + 16659168043472640 * σ
        + 100269560725012224 := by
    linarith [h0, pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4, pow_nonneg h0 5,
      pow_nonneg h0 6, pow_nonneg h0 7]
  have hEq : (Epoly ℝ 7 7 θA θB).eval (-(σ + 117)) =
      -5040 * σ ^ 7 - 3527316 * σ ^ 6 - 1031242540 * σ ^ 5 - 161769520119 * σ ^ 4
        - 14471205382512 * σ ^ 3 - 714901006709856 * σ ^ 2 - 16659168043472640 * σ
        - 100269560725012224 := by
    rw [E77_val θA θB σ (-(σ + 117)) hσ]
    ring
  linarith [hN, hEq]

theorem E77_ord0 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 86) / 13) < (0 : ℝ) := by
  linarith

theorem E77_ord1 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 130) / 11) < (-(2 * σ + 86) / 13) := by
  linarith

theorem E77_ord2 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 172) / 9) < (-(2 * σ + 130) / 11) := by
  linarith

theorem E77_ord3 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 207) / 7) < (-(2 * σ + 172) / 9) := by
  linarith

theorem E77_ord4 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 223) / 5) < (-(2 * σ + 207) / 7) := by
  linarith

theorem E77_ord5 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(2 * σ + 203) / 3) < (-(2 * σ + 223) / 5) := by
  linarith

theorem E77_ord6 (σ : ℝ) (h0 : 0 ≤ σ) :
    (-(σ + 117)) < (-(2 * σ + 203) / 3) := by
  linarith

theorem E77_roots (θA θB σ : ℝ) (hσ : θA * 7 + θB * 7 = σ) (h0 : 0 ≤ σ) :
    ∃ x1 x2 x3 x4 x5 x6 x7 : ℝ,
      x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < x5 ∧ x5 < x6 ∧ x6 < x7 ∧
        (Epoly ℝ 7 7 θA θB).eval x1 = 0 ∧ (Epoly ℝ 7 7 θA θB).eval x2 = 0 ∧
        (Epoly ℝ 7 7 θA θB).eval x3 = 0 ∧ (Epoly ℝ 7 7 θA θB).eval x4 = 0 ∧
        (Epoly ℝ 7 7 θA θB).eval x5 = 0 ∧ (Epoly ℝ 7 7 θA θB).eval x6 = 0 ∧
        (Epoly ℝ 7 7 θA θB).eval x7 = 0 := by
  have hc : ∀ s : Set ℝ, ContinuousOn (fun x : ℝ => (Epoly ℝ 7 7 θA θB).eval x) s :=
    fun _ => (Epoly ℝ 7 7 θA θB).continuousOn
  obtain ⟨y0, hy0, hr0⟩ := intermediate_value_Ioo
    (le_of_lt (E77_ord0 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep1 θA θB σ hσ h0, E77_sep0 θA θB σ hσ h0⟩)
  obtain ⟨y1, hy1, hr1⟩ := intermediate_value_Ioo'
    (le_of_lt (E77_ord1 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep1 θA θB σ hσ h0, E77_sep2 θA θB σ hσ h0⟩)
  obtain ⟨y2, hy2, hr2⟩ := intermediate_value_Ioo
    (le_of_lt (E77_ord2 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep3 θA θB σ hσ h0, E77_sep2 θA θB σ hσ h0⟩)
  obtain ⟨y3, hy3, hr3⟩ := intermediate_value_Ioo'
    (le_of_lt (E77_ord3 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep3 θA θB σ hσ h0, E77_sep4 θA θB σ hσ h0⟩)
  obtain ⟨y4, hy4, hr4⟩ := intermediate_value_Ioo
    (le_of_lt (E77_ord4 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep5 θA θB σ hσ h0, E77_sep4 θA θB σ hσ h0⟩)
  obtain ⟨y5, hy5, hr5⟩ := intermediate_value_Ioo'
    (le_of_lt (E77_ord5 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep5 θA θB σ hσ h0, E77_sep6 θA θB σ hσ h0⟩)
  obtain ⟨y6, hy6, hr6⟩ := intermediate_value_Ioo
    (le_of_lt (E77_ord6 σ h0)) (hc _)
    (Set.mem_Ioo.mpr ⟨E77_sep7 θA θB σ hσ h0, E77_sep6 θA θB σ hσ h0⟩)
  rw [Set.mem_Ioo] at hy0 hy1 hy2 hy3 hy4 hy5 hy6
  exact ⟨ y6, y5, y4, y3, y2, y1, y0, lt_trans hy6.2 hy5.1, lt_trans hy5.2 hy4.1,
    lt_trans hy4.2 hy3.1, lt_trans hy3.2 hy2.1, lt_trans hy2.2 hy1.1, lt_trans hy1.2 hy0.1, hr6,
    hr5, hr4, hr3, hr2, hr1, hr0⟩

theorem E77_splits_and_card (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 7 7 θA θB).roots = 7 ∧ (Epoly ℝ 7 7 θA θB).Splits := by
  have h0 : (0 : ℝ) ≤ θA * 7 + θB * 7 := by linarith
  obtain ⟨ x1, x2, x3, x4, x5, x6, x7, o0, o1, o2, o3, o4, o5, r0, r1, r2, r3, r4, r5,
    r6⟩ := E77_roots θA θB _ rfl h0
  have hdeg : (Epoly ℝ 7 7 θA θB).natDegree = 7 := by
    have h := natDegree_Epoly (F := ℝ) (i := 7) (j := 7) (by norm_num) (by norm_num) hA hB
    simpa using h
  have hne : (Epoly ℝ 7 7 θA θB) ≠ 0 := Epoly_ne_zero (by norm_num) (by norm_num) hA hB
  have hcard : ({x1, x2, x3, x4, x5, x6, x7} : Finset ℝ).card = 7 := by
    have h02 : x1 < x3 := by linarith
    have h03 : x1 < x4 := by linarith
    have h04 : x1 < x5 := by linarith
    have h05 : x1 < x6 := by linarith
    have h06 : x1 < x7 := by linarith
    have h13 : x2 < x4 := by linarith
    have h14 : x2 < x5 := by linarith
    have h15 : x2 < x6 := by linarith
    have h16 : x2 < x7 := by linarith
    have h24 : x3 < x5 := by linarith
    have h25 : x3 < x6 := by linarith
    have h26 : x3 < x7 := by linarith
    have h35 : x4 < x6 := by linarith
    have h36 : x4 < x7 := by linarith
    have h46 : x5 < x7 := by linarith
    rw [Finset.card_insert_of_notMem (by simp [o0.ne, h02.ne, h03.ne, h04.ne, h05.ne, h06.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o1.ne, h13.ne, h14.ne, h15.ne, h16.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o2.ne, h24.ne, h25.ne, h26.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o3.ne, h35.ne, h36.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o4.ne, h46.ne])]
    rw [Finset.card_insert_of_notMem (by simp [o5.ne])]
    rw [Finset.card_singleton]
  obtain ⟨hcards, hsplits⟩ := card_roots_eq_of_card_le hne
    ({x1, x2, x3, x4, x5, x6, x7} : Finset ℝ) (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (le_of_eq (by rw [hdeg, hcard]))
  exact ⟨by rw [hcards, hdeg], hsplits⟩

theorem E77_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (Epoly ℝ 7 7 θA θB).Splits := (E77_splits_and_card θA θB hA hB).2

theorem card_roots_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (Epoly ℝ 7 7 θA θB).roots = 7 := (E77_splits_and_card θA θB hA hB).1

theorem roots_neg_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (Epoly ℝ 7 7 θA θB).roots) : x < 0 := by
  rw [mem_roots (Epoly_ne_zero (by norm_num) (by norm_num) hA hB)] at hx
  exact Epoly_root_neg (by norm_num) (by norm_num) hA hB hx

end Rhone.Algebra.GaloisDegreeSeven
