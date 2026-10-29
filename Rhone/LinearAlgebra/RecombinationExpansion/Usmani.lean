/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination

/-! # Usmani's inverse of a tridiagonal matrix -/

@[expose] public section

namespace Rhone.LinearAlgebra.RecombinationExpansion

open Matrix Tridiag

variable {R : Type*} [CommRing R]

def Qc (d b c : ℕ → R) (n s : ℕ) : R :=
  if s ≤ n then (tridFrom d b c s (n - s)).det else 0

theorem Qc_of_le (d b c : ℕ → R) {n s : ℕ} (h : s ≤ n) :
    Qc d b c n s = (tridFrom d b c s (n - s)).det := ite_eq_left h

theorem Qc_of_gt (d b c : ℕ → R) {n s : ℕ} (h : n < s) : Qc d b c n s = 0 :=
  ite_eq_right (by omega)

@[simp]
theorem Qc_self (d b c : ℕ → R) (n : ℕ) : Qc d b c n n = 1 := by
  rw [Qc_of_le d b c (le_refl n), Nat.sub_self, det_tridFrom_zero]

@[simp]
theorem Qc_succ_self (d b c : ℕ → R) (n : ℕ) : Qc d b c n (n + 1) = 0 :=
  Qc_of_gt d b c (by omega)

theorem Qc_rec (d b c : ℕ → R) {n s : ℕ} (h : s < n) :
    Qc d b c n s = d s * Qc d b c n (s + 1) - b s * c s * Qc d b c n (s + 2) := by
  rcases Nat.lt_or_ge (s + 1) n with h2 | h2
  · have e0 : n - s = (n - s - 2) + 2 := by omega
    have e1 : n - (s + 1) = (n - s - 2) + 1 := by omega
    have e2 : n - (s + 2) = n - s - 2 := by omega
    rw [Qc_of_le d b c (le_of_lt h), Qc_of_le d b c (by omega : s + 1 ≤ n),
      Qc_of_le d b c (by omega : s + 2 ≤ n), e0, e1, e2, det_tridFrom_add_two]
  · have hs : s + 1 = n := by omega
    have e0 : n - s = 1 := by omega
    have e3 : s + 2 = n + 1 := by omega
    rw [Qc_of_le d b c (le_of_lt h), e0, det_tridFrom_one, hs, Qc_self, e3, Qc_succ_self]
    ring

theorem trid_row_range (d b c : ℕ → R) {n : ℕ} (w : ℕ → R) (hw : w n = 0) {i : ℕ}
    (hi : i < n) :
    (∑ k : Fin n, tridEntry d b c i (k : ℕ) * w (k : ℕ))
      = ∑ k ∈ Finset.range (i + 2), tridEntry d b c i k * w k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => tridEntry d b c i k * w k) n]
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · have hsub : Finset.range (i + 2) ⊆ Finset.range n := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    refine (Finset.sum_subset hsub ?_).symm
    intro x _ hx
    have hx' : i + 2 ≤ x := by
      by_contra hc
      exact hx (Finset.mem_range.2 (by omega))
    rw [tridEntry_of_lt d b c (by omega), zero_mul]
  · have hn : n = i + 1 := by omega
    subst hn
    conv_rhs => rw [Finset.sum_range_succ]
    rw [hw, mul_zero, add_zero]

theorem trid_row_zero (d b c : ℕ → R) (w : ℕ → R) :
    (∑ k ∈ Finset.range 2, tridEntry d b c 0 k * w k) = d 0 * w 0 + b 0 * w 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, tridEntry_of_eq d b c rfl,
    tridEntry_of_succ d b c rfl]

theorem trid_row_succ (d b c : ℕ → R) (w : ℕ → R) (i : ℕ) :
    (∑ k ∈ Finset.range (i + 3), tridEntry d b c (i + 1) k * w k)
      = c i * w i + d (i + 1) * w (i + 1) + b (i + 1) * w (i + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero (s := Finset.range i) (fun k hk => ?_),
    tridEntry_of_pred d b c rfl, tridEntry_of_eq d b c rfl, tridEntry_of_succ d b c rfl,
    zero_add]
  rw [Finset.mem_range] at hk
  rw [tridEntry_of_gt d b c (by omega), zero_mul]

def runProd (f : ℕ → R) (lo hi : ℕ) : R := ∏ s ∈ Finset.Ico lo hi, f s

@[simp]
theorem runProd_self (f : ℕ → R) (lo : ℕ) : runProd f lo lo = 1 := by
  simp [runProd]

theorem runProd_succ_left (f : ℕ → R) {lo hi : ℕ} (h : lo < hi) :
    runProd f lo hi = f lo * runProd f (lo + 1) hi :=
  Finset.prod_eq_prod_Ico_succ_bot h f

theorem runProd_succ_right (f : ℕ → R) {lo hi : ℕ} (h : lo ≤ hi) :
    runProd f lo (hi + 1) = runProd f lo hi * f hi :=
  Finset.prod_Ico_succ_top h f

def usmaniEntry (d b c : ℕ → R) (n i j : ℕ) : R :=
  if i ≤ j then (-1) ^ (i + j) * runProd b i j * cont d b c i * Qc d b c n (j + 1)
  else (-1) ^ (i + j) * runProd c j i * cont d b c j * Qc d b c n (i + 1)

theorem usmaniEntry_of_le (d b c : ℕ → R) (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    usmaniEntry d b c n i j
      = (-1) ^ (i + j) * runProd b i j * cont d b c i * Qc d b c n (j + 1) :=
  ite_eq_left h

theorem usmaniEntry_of_ge (d b c : ℕ → R) (n : ℕ) {i j : ℕ} (h : j ≤ i) :
    usmaniEntry d b c n i j
      = (-1) ^ (i + j) * runProd c j i * cont d b c j * Qc d b c n (i + 1) := by
  rcases Nat.lt_or_ge j i with h' | h'
  · exact ite_eq_right (by omega)
  · have hij : i = j := by omega
    subst hij
    rw [usmaniEntry_of_le d b c n (le_refl i), runProd_self, runProd_self]

theorem usmaniEntry_top (d b c : ℕ → R) {n j : ℕ} (h : j < n) : usmaniEntry d b c n n j = 0 := by
  rw [usmaniEntry_of_ge d b c n (le_of_lt h), Qc_succ_self, mul_zero]

def usmani (d b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => usmaniEntry d b c n (i : ℕ) (j : ℕ)

@[simp]
theorem usmani_apply (d b c : ℕ → R) (n : ℕ) (i j : Fin n) :
    usmani d b c n i j = usmaniEntry d b c n (i : ℕ) (j : ℕ) := rfl

theorem cont_mul_Qc (d b c : ℕ → R) (n : ℕ) :
    ∀ m i : ℕ, i + m + 1 = n →
      cont d b c (i + 1) * Qc d b c n (i + 1)
          - b i * c i * cont d b c i * Qc d b c n (i + 2) = cont d b c n := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have h1 : i + 1 = n := by omega
    have h2 : i + 2 = n + 1 := by omega
    rw [h1, Qc_self, h2, Qc_succ_self]
    ring
  | succ k ih =>
    intro i hi
    have ih' := ih (i + 1) (by omega)
    have hQ : Qc d b c n (i + 1)
        = d (i + 1) * Qc d b c n (i + 2) - b (i + 1) * c (i + 1) * Qc d b c n (i + 3) :=
      Qc_rec d b c (by omega)
    have hP : cont d b c (i + 2)
        = d (i + 1) * cont d b c (i + 1) - b i * c i * cont d b c i := rfl
    rw [hQ, ← ih', hP]
    ring

theorem cont_mul_Qc' (d b c : ℕ → R) {n i : ℕ} (h : i < n) :
    cont d b c (i + 1) * Qc d b c n (i + 1)
      - b i * c i * cont d b c i * Qc d b c n (i + 2) = cont d b c n :=
  cont_mul_Qc d b c n (n - i - 1) i (by omega)

private theorem neg_one_pow_two_mul (k : ℕ) : (-1 : R) ^ (2 * k) = 1 :=
  Even.neg_one_pow (even_two_mul k)

private theorem neg_one_pow_succ_add (i j : ℕ) :
    (-1 : R) ^ (i + 1 + j) = -((-1 : R) ^ (i + j)) := by
  rw [show i + 1 + j = (i + j) + 1 from by omega, pow_succ]
  ring

private theorem neg_one_pow_add_two (i j : ℕ) :
    (-1 : R) ^ (i + 2 + j) = (-1 : R) ^ (i + j) := by
  rw [show i + 2 + j = (i + j) + 2 from by omega, pow_succ, pow_succ]
  ring

private theorem row_upper (d b c : ℕ → R) {n i j : ℕ} (hi : i < n) (hij : i < j) :
    (∑ k ∈ Finset.range (i + 2), tridEntry d b c i k * usmaniEntry d b c n k j) = 0 := by
  match i with
  | 0 =>
    rw [trid_row_zero, usmaniEntry_of_le d b c n (Nat.zero_le j),
      usmaniEntry_of_le d b c n (by omega : 1 ≤ j),
      runProd_succ_left b (by omega : 0 < j)]
    have h1 : cont d b c 0 = (1 : R) := rfl
    have h2 : cont d b c 1 = d 0 := rfl
    rw [h1, h2, neg_one_pow_succ_add 0 j]
    ring
  | (i' + 1) =>
    rw [show i' + 1 + 2 = i' + 3 from by omega, trid_row_succ,
      usmaniEntry_of_le d b c n (by omega : i' ≤ j),
      usmaniEntry_of_le d b c n (by omega : i' + 1 ≤ j),
      usmaniEntry_of_le d b c n (by omega : i' + 2 ≤ j),
      runProd_succ_left b (by omega : i' < j),
      runProd_succ_left b (by omega : i' + 1 < j),
      neg_one_pow_succ_add i' j, neg_one_pow_add_two i' j]
    have hP : cont d b c (i' + 2)
        = d (i' + 1) * cont d b c (i' + 1) - b i' * c i' * cont d b c i' := rfl
    rw [hP]
    ring

private theorem row_lower (d b c : ℕ → R) {n i j : ℕ} (hi : i < n) (hij : j < i) :
    (∑ k ∈ Finset.range (i + 2), tridEntry d b c i k * usmaniEntry d b c n k j) = 0 := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [show i' + 1 + 2 = i' + 3 from by omega, trid_row_succ,
    usmaniEntry_of_ge d b c n (by omega : j ≤ i'),
    usmaniEntry_of_ge d b c n (by omega : j ≤ i' + 1),
    usmaniEntry_of_ge d b c n (by omega : j ≤ i' + 2),
    runProd_succ_right c (by omega : j ≤ i' + 1),
    runProd_succ_right c (by omega : j ≤ i'),
    neg_one_pow_succ_add i' j, neg_one_pow_add_two i' j]
  have hQ : Qc d b c n (i' + 1)
      = d (i' + 1) * Qc d b c n (i' + 2) - b (i' + 1) * c (i' + 1) * Qc d b c n (i' + 3) :=
    Qc_rec d b c (by omega)
  rw [hQ]
  ring

private theorem row_diag (d b c : ℕ → R) {n i : ℕ} (hi : i < n) :
    (∑ k ∈ Finset.range (i + 2), tridEntry d b c i k * usmaniEntry d b c n k i)
      = cont d b c n := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have key := cont_mul_Qc' d b c hi
    have h0 : cont d b c 0 = (1 : R) := rfl
    have h1 : cont d b c (0 + 1) = d 0 := rfl
    rw [h0, h1] at key
    have e0 : usmaniEntry d b c n 0 0 = Qc d b c n (0 + 1) := by
      rw [usmaniEntry_of_le d b c n (le_refl 0), runProd_self, h0]
      norm_num
    have e1 : usmaniEntry d b c n 1 0 = -(c 0 * Qc d b c n (0 + 2)) := by
      rw [usmaniEntry_of_ge d b c n (by omega : (0 : ℕ) ≤ 1),
        runProd_succ_right c (le_refl 0), runProd_self, h0,
        show (1 : ℕ) + 1 = 0 + 2 from by omega]
      norm_num
    rw [trid_row_zero, e0, e1]
    linear_combination key
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have key := cont_mul_Qc' d b c hi
    have hP : cont d b c (i' + 2)
        = d (i' + 1) * cont d b c (i' + 1) - b i' * c i' * cont d b c i' := rfl
    have e0 : usmaniEntry d b c n i' (i' + 1)
        = -(b i' * cont d b c i' * Qc d b c n (i' + 1 + 1)) := by
      rw [usmaniEntry_of_le d b c n (by omega : i' ≤ i' + 1),
        runProd_succ_right b (le_refl i'), runProd_self,
        show i' + (i' + 1) = 2 * i' + 1 from by omega, pow_succ, neg_one_pow_two_mul]
      ring
    have e1 : usmaniEntry d b c n (i' + 1) (i' + 1)
        = cont d b c (i' + 1) * Qc d b c n (i' + 1 + 1) := by
      rw [usmaniEntry_of_le d b c n (le_refl (i' + 1)), runProd_self,
        show i' + 1 + (i' + 1) = 2 * (i' + 1) from by omega, neg_one_pow_two_mul]
      ring
    have e2 : usmaniEntry d b c n (i' + 2) (i' + 1)
        = -(c (i' + 1) * cont d b c (i' + 1) * Qc d b c n (i' + 2 + 1)) := by
      rw [usmaniEntry_of_ge d b c n (by omega : i' + 1 ≤ i' + 2),
        runProd_succ_right c (le_refl (i' + 1)), runProd_self,
        show i' + 2 + (i' + 1) = 2 * (i' + 1) + 1 from by omega, pow_succ, neg_one_pow_two_mul]
      ring
    rw [show i' + 1 + 2 = i' + 3 from by omega, trid_row_succ, e0, e1, e2]
    linear_combination key - Qc d b c n (i' + 1 + 1) * hP

theorem trid_mul_usmani (d b c : ℕ → R) (n : ℕ) :
    trid d b c n * usmani d b c n = (cont d b c n) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext I J
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hi : (I : ℕ) < n := I.isLt
  have hj : (J : ℕ) < n := J.isLt
  have hstep : ∀ k : Fin n, trid d b c n I k * usmani d b c n k J
      = tridEntry d b c (I : ℕ) (k : ℕ) * usmaniEntry d b c n (k : ℕ) (J : ℕ) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun k _ => hstep k),
    trid_row_range d b c (fun k => usmaniEntry d b c n k (J : ℕ))
      (usmaniEntry_top d b c hj) hi]
  rcases Nat.lt_trichotomy (I : ℕ) (J : ℕ) with h | h | h
  · rw [row_upper d b c hi h, ite_eq_right (fun hIJ => by rw [hIJ] at h; omega), mul_zero]
  · have hIJ : I = J := Fin.ext h
    rw [← h, row_diag d b c hi, ite_eq_left hIJ, mul_one]
  · rw [row_lower d b c hi h, ite_eq_right (fun hIJ => by rw [hIJ] at h; omega), mul_zero]

theorem tridEntry_swap (d b c : ℕ → R) (s t : ℕ) :
    tridEntry d c b s t = tridEntry d b c t s := by
  rcases eq_or_ne t s with h | h
  · rw [tridEntry_of_eq d c b h, tridEntry_of_eq d b c h.symm, h]
  rcases eq_or_ne t (s + 1) with h2 | h2
  · rw [tridEntry_of_succ d c b h2, tridEntry_of_pred d b c h2]
  rcases eq_or_ne s (t + 1) with h3 | h3
  · rw [tridEntry_of_pred d c b h3, tridEntry_of_succ d b c h3]
  rcases Nat.lt_or_ge (s + 1) t with h4 | h4
  · rw [tridEntry_of_lt d c b h4, tridEntry_of_gt d b c h4]
  · have h5 : t + 1 < s := by omega
    rw [tridEntry_of_gt d c b h5, tridEntry_of_lt d b c h5]

theorem trid_transpose (d b c : ℕ → R) (n : ℕ) : (trid d b c n)ᵀ = trid d c b n := by
  ext p q
  rw [Matrix.transpose_apply, trid_apply, trid_apply]
  exact (tridEntry_swap d b c (p : ℕ) (q : ℕ)).symm

theorem tridFrom_transpose (d b c : ℕ → R) (s m : ℕ) :
    tridFrom d c b s m = (tridFrom d b c s m)ᵀ := by
  ext p q
  rw [Matrix.transpose_apply, tridFrom_apply, tridFrom_apply]
  exact tridEntry_swap d b c _ _

theorem cont_swap (d b c : ℕ → R) (n : ℕ) : cont d c b n = cont d b c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
      change d (k + 1) * cont d c b (k + 1) - c k * b k * cont d c b k
        = d (k + 1) * cont d b c (k + 1) - b k * c k * cont d b c k
      rw [ih (k + 1) (by omega), ih k (by omega)]
      ring

theorem Qc_swap (d b c : ℕ → R) (n s : ℕ) : Qc d c b n s = Qc d b c n s := by
  unfold Qc
  split_ifs with h
  · rw [tridFrom_transpose]
    exact Matrix.det_transpose _
  · rfl

theorem usmani_transpose (d b c : ℕ → R) (n : ℕ) : (usmani d b c n)ᵀ = usmani d c b n := by
  ext p q
  rw [Matrix.transpose_apply, usmani_apply, usmani_apply]
  rcases Nat.lt_or_ge (q : ℕ) (p : ℕ) with h | h
  · rw [usmaniEntry_of_le d b c n (le_of_lt h), usmaniEntry_of_ge d c b n (le_of_lt h),
      cont_swap, Qc_swap, add_comm ((q : ℕ)) ((p : ℕ))]
  · rw [usmaniEntry_of_ge d b c n h, usmaniEntry_of_le d c b n h, cont_swap, Qc_swap,
      add_comm ((q : ℕ)) ((p : ℕ))]

theorem usmani_mul_trid (d b c : ℕ → R) (n : ℕ) :
    usmani d b c n * trid d b c n = (cont d b c n) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h2 := congrArg Matrix.transpose (trid_mul_usmani d c b n)
  rw [Matrix.transpose_mul, trid_transpose, usmani_transpose, Matrix.transpose_smul,
    Matrix.transpose_one, cont_swap] at h2
  exact h2

section Field

variable {F : Type*} [Field F]

theorem inv_trid (d b c : ℕ → F) (n : ℕ) (h : cont d b c n ≠ 0) :
    (trid d b c n)⁻¹ = (cont d b c n)⁻¹ • usmani d b c n := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, trid_mul_usmani, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem inv_trid_apply_of_le (d b c : ℕ → F) {n : ℕ} (h : cont d b c n ≠ 0) (i j : Fin n)
    (hij : (i : ℕ) ≤ (j : ℕ)) :
    (trid d b c n)⁻¹ i j
      = (-1) ^ ((i : ℕ) + (j : ℕ)) * runProd b (i : ℕ) (j : ℕ) * cont d b c (i : ℕ)
          * Qc d b c n ((j : ℕ) + 1) / cont d b c n := by
  rw [inv_trid d b c n h, Matrix.smul_apply, usmani_apply, usmaniEntry_of_le d b c n hij,
    smul_eq_mul, div_eq_inv_mul]

theorem inv_trid_apply_of_ge (d b c : ℕ → F) {n : ℕ} (h : cont d b c n ≠ 0) (i j : Fin n)
    (hij : (j : ℕ) ≤ (i : ℕ)) :
    (trid d b c n)⁻¹ i j
      = (-1) ^ ((i : ℕ) + (j : ℕ)) * runProd c (j : ℕ) (i : ℕ) * cont d b c (j : ℕ)
          * Qc d b c n ((i : ℕ) + 1) / cont d b c n := by
  rw [inv_trid d b c n h, Matrix.smul_apply, usmani_apply, usmaniEntry_of_ge d b c n hij,
    smul_eq_mul, div_eq_inv_mul]

theorem mulVec_usmani_eq (d b c : ℕ → F) {n : ℕ} (h : cont d b c n ≠ 0)
    {Φ Rv : Fin n → F} (hΦ : trid d b c n *ᵥ Φ = Rv) :
    Φ = (cont d b c n)⁻¹ • (usmani d b c n *ᵥ Rv) := by
  rw [← hΦ, Matrix.mulVec_mulVec, usmani_mul_trid, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ h, one_smul]

end Field

end Rhone.LinearAlgebra.RecombinationExpansion
