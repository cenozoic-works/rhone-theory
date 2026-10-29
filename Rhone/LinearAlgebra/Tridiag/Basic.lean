/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Tridiagonal matrices and the continuant recurrence -/

@[expose] public section

namespace Rhone.LinearAlgebra.Tridiag

open Matrix

variable {R : Type*} [CommRing R]

def tridEntry (d b c : ℕ → R) (s t : ℕ) : R :=
  if t = s then d s else if t = s + 1 then b s else if s = t + 1 then c t else 0

def trid (d b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun s t => tridEntry d b c (s : ℕ) (t : ℕ)

def tridFrom (d b c : ℕ → R) (s n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun p q => tridEntry d b c ((p : ℕ) + s) ((q : ℕ) + s)

@[simp]
theorem trid_apply (d b c : ℕ → R) (n : ℕ) (s t : Fin n) :
    trid d b c n s t = tridEntry d b c (s : ℕ) (t : ℕ) := rfl

@[simp]
theorem tridFrom_apply (d b c : ℕ → R) (s n : ℕ) (p q : Fin n) :
    tridFrom d b c s n p q = tridEntry d b c ((p : ℕ) + s) ((q : ℕ) + s) := rfl

theorem tridFrom_zero (d b c : ℕ → R) (n : ℕ) : tridFrom d b c 0 n = trid d b c n := by
  ext p q; simp

theorem tridEntry_of_eq (d b c : ℕ → R) {s t : ℕ} (h : t = s) : tridEntry d b c s t = d s := by
  simp [tridEntry, h]

theorem tridEntry_of_succ (d b c : ℕ → R) {s t : ℕ} (h : t = s + 1) :
    tridEntry d b c s t = b s := by
  unfold tridEntry
  rw [ite_eq_right (by omega), ite_eq_left h]

theorem tridEntry_of_pred (d b c : ℕ → R) {s t : ℕ} (h : s = t + 1) :
    tridEntry d b c s t = c t := by
  unfold tridEntry
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

theorem tridEntry_of_lt (d b c : ℕ → R) {s t : ℕ} (h : s + 1 < t) :
    tridEntry d b c s t = 0 := by
  unfold tridEntry
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem tridEntry_of_gt (d b c : ℕ → R) {s t : ℕ} (h : t + 1 < s) :
    tridEntry d b c s t = 0 := by
  unfold tridEntry
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), ite_eq_left h,
      Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using Nat.not_lt.mp h),
      ite_eq_right h,
      Fin.val_succ]

theorem tridFrom_submatrix_succ (d b c : ℕ → R) (s n : ℕ) :
    (tridFrom d b c s (n + 1)).submatrix Fin.succ Fin.succ = tridFrom d b c (s + 1) n := by
  ext p q
  simp only [Matrix.submatrix_apply, tridFrom_apply, Fin.val_succ]
  congr 1 <;> omega

theorem tridFrom_submatrix_one (d b c : ℕ → R) (s n : ℕ) :
    (((tridFrom d b c s (n + 2)).submatrix Fin.succ
        ((1 : Fin (n + 2)).succAbove)).submatrix Fin.succ Fin.succ)
      = tridFrom d b c (s + 2) n := by
  have hone : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
  ext p q
  have hq : (((1 : Fin (n + 2)).succAbove q.succ : Fin (n + 2)) : ℕ) = (q : ℕ) + 2 := by
    rw [val_succAbove, hone, ite_eq_right (by simp [Fin.val_succ]), Fin.val_succ]
  simp only [Matrix.submatrix_apply, tridFrom_apply, hq, Fin.val_succ]
  congr 1 <;> omega

@[simp]
theorem det_tridFrom_zero (d b c : ℕ → R) (s : ℕ) : (tridFrom d b c s 0).det = 1 :=
  Matrix.det_fin_zero

@[simp]
theorem det_tridFrom_one (d b c : ℕ → R) (s : ℕ) : (tridFrom d b c s 1).det = d s := by
  rw [Matrix.det_fin_one, tridFrom_apply, Fin.val_zero, Nat.zero_add]
  exact tridEntry_of_eq d b c rfl

theorem det_tridFrom_add_two (d b c : ℕ → R) (s n : ℕ) :
    (tridFrom d b c s (n + 2)).det
      = d s * (tridFrom d b c (s + 1) (n + 1)).det
        - b s * c s * (tridFrom d b c (s + 2) n).det := by
  have hone : ((1 : Fin (n + 2)) : ℕ) = 1 := by simp
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  have hzero : ∀ j : Fin n,
      (-1 : R) ^ ((j.succ.succ : Fin (n + 2)) : ℕ) *
          tridFrom d b c s (n + 2) 0 j.succ.succ *
          ((tridFrom d b c s (n + 2)).submatrix Fin.succ (j.succ.succ.succAbove)).det = 0 := by
    intro j
    have h : tridFrom d b c s (n + 2) 0 j.succ.succ = 0 := by
      simp only [tridFrom_apply, Fin.val_zero, Fin.val_succ, Nat.zero_add]
      exact tridEntry_of_lt d b c (by omega)
    rw [h, mul_zero, zero_mul]
  rw [Finset.sum_eq_zero (fun j _ => hzero j), add_zero]
  have h0 : tridFrom d b c s (n + 2) 0 0 = d s := by
    rw [tridFrom_apply, Fin.val_zero, Nat.zero_add]
    exact tridEntry_of_eq d b c rfl
  have h0' : (tridFrom d b c s (n + 2)).submatrix Fin.succ ((0 : Fin (n + 2)).succAbove)
      = tridFrom d b c (s + 1) (n + 1) := by
    rw [Fin.succAbove_zero]
    exact tridFrom_submatrix_succ d b c s (n + 1)
  have h1 : tridFrom d b c s (n + 2) 0 1 = b s := by
    rw [tridFrom_apply, Fin.val_zero, Nat.zero_add, hone]
    refine tridEntry_of_succ d b c ?_
    omega
  set B := (tridFrom d b c s (n + 2)).submatrix Fin.succ ((1 : Fin (n + 2)).succAbove) with hB
  have hBcol : ∀ p : Fin (n + 1), B p 0 = if (p : ℕ) = 0 then c s else 0 := by
    intro p
    have hz : (((1 : Fin (n + 2)).succAbove (0 : Fin (n + 1)) : Fin (n + 2)) : ℕ) = 0 := by
      rw [val_succAbove, hone, ite_eq_left (by simp)]
      simp
    simp only [hB, Matrix.submatrix_apply, tridFrom_apply, hz, Fin.val_succ, Nat.zero_add]
    by_cases hp : (p : ℕ) = 0
    · rw [ite_eq_left hp, hp]
      exact tridEntry_of_pred d b c (by omega)
    · rw [ite_eq_right hp]
      exact tridEntry_of_gt d b c (by omega)
  have hB00 : B 0 0 = c s := by rw [hBcol]; simp
  have hBdet : B.det = c s * (tridFrom d b c (s + 2) n).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ p : Fin n, (-1 : R) ^ ((p.succ : Fin (n + 1)) : ℕ) * B p.succ 0 *
        (B.submatrix (p.succ.succAbove) Fin.succ).det = 0 := by
      intro p
      rw [hBcol, ite_eq_right (by simp [Fin.val_succ]), mul_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun p _ => hz p), add_zero, hB00, Fin.succAbove_zero, Fin.val_zero,
      pow_zero, one_mul, hB, tridFrom_submatrix_one]
  rw [h0, h0', h1, hBdet, hone, Fin.val_zero]
  ring

def revSeq (f : ℕ → R) (N : ℕ) : ℕ → R := fun s => f (N - 1 - s)

omit [CommRing R] in
theorem revSeq_shift (f : ℕ → R) (N k : ℕ) :
    (fun u => revSeq f N (u + k)) = revSeq f (N - k) := by
  funext u
  change f (N - 1 - (u + k)) = f (N - k - 1 - u)
  congr 1
  omega

theorem trid_submatrix_rev (d b c : ℕ → R) (N : ℕ) :
    (trid d b c N).submatrix Fin.rev Fin.rev
      = trid (revSeq d N) (revSeq c (N - 1)) (revSeq b (N - 1)) N := by
  ext p q
  have hp : (p : ℕ) < N := p.isLt
  have hq : (q : ℕ) < N := q.isLt
  simp only [Matrix.submatrix_apply, trid_apply, Fin.val_rev, tridEntry, revSeq]
  split_ifs <;> first | (congr 1; omega) | omega | rfl

theorem det_trid_rev (d b c : ℕ → R) (N : ℕ) :
    (trid (revSeq d N) (revSeq c (N - 1)) (revSeq b (N - 1)) N).det = (trid d b c N).det := by
  rw [← trid_submatrix_rev]
  exact Matrix.det_submatrix_equiv_self (Fin.revPerm) _

theorem tridFrom_eq_trid_shift (d b c : ℕ → R) (s n : ℕ) :
    tridFrom d b c s n
      = trid (fun u => d (u + s)) (fun u => b (u + s)) (fun u => c (u + s)) n := by
  ext p q
  simp only [tridFrom_apply, trid_apply, tridEntry]
  split_ifs <;> first | rfl | omega

theorem det_trid_add_two (d b c : ℕ → R) (n : ℕ) :
    (trid d b c (n + 2)).det
      = d (n + 1) * (trid d b c (n + 1)).det - b n * c n * (trid d b c n).det := by
  rw [← det_trid_rev d b c (n + 2), ← tridFrom_zero, det_tridFrom_add_two,
    tridFrom_eq_trid_shift, tridFrom_eq_trid_shift, revSeq_shift, revSeq_shift, revSeq_shift,
    revSeq_shift, revSeq_shift, revSeq_shift]
  have h1 : (trid (revSeq d (n + 2 - 1)) (revSeq c (n + 2 - 1 - 1)) (revSeq b (n + 2 - 1 - 1))
      (n + 1)).det = (trid d b c (n + 1)).det := det_trid_rev d b c (n + 1)
  have h2 : (trid (revSeq d (n + 2 - 2)) (revSeq c (n + 2 - 1 - 2)) (revSeq b (n + 2 - 1 - 2))
      n).det = (trid d b c n).det := det_trid_rev d b c n
  rw [h1, h2]
  simp only [revSeq]
  rw [show n + 2 - 1 - 0 = n + 1 from by omega, show n + 2 - 1 - 1 - 0 = n from by omega]
  ring

def cont (d b c : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => d 0
  | (r + 2) => d (r + 1) * cont d b c (r + 1) - b r * c r * cont d b c r

theorem det_trid_eq_cont (d b c : ℕ → R) (n : ℕ) : (trid d b c n).det = cont d b c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [← tridFrom_zero, det_tridFrom_zero]; rfl
    | 1 => rw [← tridFrom_zero, det_tridFrom_one]; rfl
    | (k + 2) =>
      rw [det_trid_add_two, ih (k + 1) (by omega), ih k (by omega), cont]

end Rhone.LinearAlgebra.Tridiag
