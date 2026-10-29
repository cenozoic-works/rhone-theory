/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Stirling
public import Rhone.Combinatorics.StirlingSetPartitions
public import Mathlib.Combinatorics.Enumerative.Stirling

/-! # Executable Stirling numbers of the second kind equal the specification -/

@[expose] public section
namespace Rhone.Computation.Stirling

private theorem getD_zipWith_mul (a b : List Nat) (k : Nat) (h : a.length = b.length) :
    (List.zipWith (· * ·) a b).getD k 0 = a.getD k 0 * b.getD k 0 := by
  induction a generalizing b k with
  | nil =>
    cases b with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      cases k with
      | zero => simp
      | succ k => simpa using ih ys k (by simpa using h)

private theorem getD_zipWith_add (a b : List Nat) (k : Nat) (h : a.length = b.length) :
    (List.zipWith (· + ·) a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  induction a generalizing b k with
  | nil =>
    cases b with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      cases k with
      | zero => simp
      | succ k => simpa using ih ys k (by simpa using h)

private theorem getD_range (m k : Nat) : (List.range m).getD k 0 = if k < m then k else 0 := by
  by_cases h : k < m
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem getD_append_zero (row : List Nat) (k : Nat) :
    (row ++ [0]).getD k 0 = row.getD k 0 := by
  induction row generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih => cases k <;> simp_all

private theorem getD_of_le (row : List Nat) (k : Nat) (h : row.length ≤ k) :
    row.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

private theorem secondStep_getD (row : List Nat) (k : Nat) :
    (secondStep row).getD k 0 =
      k * row.getD k 0 + (match k with | 0 => 0 | k + 1 => row.getD k 0) := by
  unfold secondStep
  rw [getD_zipWith_add _ _ _ (by simp), getD_zipWith_mul _ _ _ (by simp), getD_append_zero,
    getD_range]
  by_cases h : k < row.length + 1
  · cases k with
    | zero => simp
    | succ k =>
      have hk : k < row.length := by omega
      simp [h, List.getElem?_eq_getElem hk]
  · cases k with
    | zero => omega
    | succ k =>
      rw [getD_of_le row (k + 1) (by omega)]
      have h2 := getD_of_le row k (by omega)
      rw [List.getD_eq_getElem?_getD] at h2
      simp [h, h2]

theorem second_eq (n k : Nat) : second n k = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [second, secondRow]
  | succ n ih =>
    have e : second (n + 1) k =
        k * second n k + (match k with | 0 => 0 | k + 1 => second n k) :=
      secondStep_getD (secondRow n) k
    rw [e]
    cases k with
    | zero => simp [ih]
    | succ k => simp only [ih, Nat.stirlingSecond_succ_succ]

theorem second_eq_card (n k : Nat) :
    second n k = Fintype.card {P : Finpartition (Finset.univ : Finset (Fin n)) //
      P.parts.card = k} := by
  rw [second_eq, Rhone.Combinatorics.card_finpartition_eq_stirlingSecond]

example : second 5 2 = 15 ∧ second 4 3 = 6 := by decide

end Rhone.Computation.Stirling
