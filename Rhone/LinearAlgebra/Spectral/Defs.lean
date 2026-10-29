/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Slack
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The two-locus level operator `T^{(i,j)}` and the demographic epoch operator `T_e` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

theorem mulVec_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (t : Fin n) :
    (M *ᵥ v) t = ∑ s, M t s * v s :=
  Matrix.mulVec_apply_eq_sum M v t

noncomputable def Tdiag (i j : ℕ) (θA θB ρ : ℝ) (t : ℕ) : ℝ :=
  ((i : ℝ) + (j : ℝ) - (t : ℝ)) * ((i : ℝ) + (j : ℝ) - (t : ℝ) - 1)
    + (i : ℝ) * θA + (j : ℝ) * θB + ρ * (t : ℝ)

noncomputable def Tsup (i j : ℕ) (t : ℕ) : ℝ := -2 * ((i : ℝ) - (t : ℝ)) * ((j : ℝ) - (t : ℝ))

noncomputable def Tsub (ρ : ℝ) (t : ℕ) : ℝ := -(ρ * (t : ℝ))

noncomputable def T (i j : ℕ) (θA θB ρ : ℝ) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ := fun t s =>
  if (s : ℕ) = (t : ℕ) then Tdiag i j θA θB ρ (t : ℕ)
  else if (s : ℕ) = (t : ℕ) + 1 then Tsup i j (t : ℕ)
  else if (t : ℕ) = (s : ℕ) + 1 then Tsub ρ (t : ℕ)
  else 0

noncomputable def Te (i j : ℕ) (lam θA θB ρ : ℝ) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ :=
  lam⁻¹ • T i j (lam * θA) (lam * θB) (lam * ρ)

variable {i j : ℕ} {θA θB ρ : ℝ}

@[simp] theorem T_apply_diag (t : Fin (min i j + 1)) :
    T i j θA θB ρ t t = Tdiag i j θA θB ρ (t : ℕ) := by
  unfold T; rw [ite_eq_left rfl]

theorem T_apply_sup {t s : Fin (min i j + 1)} (h : (s : ℕ) = (t : ℕ) + 1) :
    T i j θA θB ρ t s = Tsup i j (t : ℕ) := by
  unfold T; rw [ite_eq_right (by omega), ite_eq_left h]

theorem T_apply_sub {t s : Fin (min i j + 1)} (h : (t : ℕ) = (s : ℕ) + 1) :
    T i j θA θB ρ t s = Tsub ρ (t : ℕ) := by
  unfold T; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

theorem T_apply_zero {t s : Fin (min i j + 1)} (h1 : (s : ℕ) ≠ (t : ℕ))
    (h2 : (s : ℕ) ≠ (t : ℕ) + 1) (h3 : (t : ℕ) ≠ (s : ℕ) + 1) :
    T i j θA θB ρ t s = 0 := by
  unfold T; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

theorem T_apply_eq_indicators (t s : Fin (min i j + 1)) :
    T i j θA θB ρ t s =
      (if (s : ℕ) = (t : ℕ) then Tdiag i j θA θB ρ (t : ℕ) else 0)
      + (if (s : ℕ) = (t : ℕ) + 1 then Tsup i j (t : ℕ) else 0)
      + (if (t : ℕ) = (s : ℕ) + 1 then Tsub ρ (t : ℕ) else 0) := by
  unfold T
  split_ifs <;> first | ring1 | (exfalso; omega)

private theorem sum_ite_val_eq {n : ℕ} (k : ℕ) (c : ℝ) :
    ∑ s : Fin n, (if (s : ℕ) = k then c else 0) = if k < n then c else 0 := by
  by_cases hk : k < n
  · have hcond : ∀ s : Fin n, ((s : ℕ) = k) ↔ (s = (⟨k, hk⟩ : Fin n)) := by
      intro s; rw [Fin.ext_iff]
    simp only [hcond, hk, ite_true]
    simp
  · simp only [hk, ite_false]
    refine Finset.sum_eq_zero fun s _ => ?_
    have := s.isLt
    rw [ite_eq_right (by omega)]

private theorem sum_ite_val_pred {n : ℕ} (t : Fin n) (c : ℝ) :
    ∑ s : Fin n, (if (t : ℕ) = (s : ℕ) + 1 then c else 0) = if (t : ℕ) = 0 then 0 else c := by
  rcases Nat.eq_zero_or_pos (t : ℕ) with h | h
  · simp only [h]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [ite_eq_right (by omega)]
  · have hk : (t : ℕ) - 1 < n := by have := t.isLt; omega
    have hcond : ∀ s : Fin n, ((t : ℕ) = (s : ℕ) + 1) ↔ (s = (⟨(t : ℕ) - 1, hk⟩ : Fin n)) := by
      intro s; rw [Fin.ext_iff]; simp only []; omega
    simp only [hcond]
    rw [ite_eq_right (by omega)]
    simp

theorem sup_factor_top {t : ℕ} (h : t = min i j) :
    ((i : ℝ) - (t : ℝ)) * ((j : ℝ) - (t : ℝ)) = 0 := by
  subst h
  rcases le_total i j with hle | hle
  · rw [min_eq_left hle]; ring
  · rw [min_eq_right hle]; ring

theorem sup_if_eq (t : Fin (min i j + 1)) :
    (if (t : ℕ) + 1 < min i j + 1 then Tsup i j (t : ℕ) else 0) = Tsup i j (t : ℕ) := by
  by_cases h : (t : ℕ) + 1 < min i j + 1
  · rw [ite_eq_left h]
  · have ht : (t : ℕ) = min i j := by have := t.isLt; omega
    rw [ite_eq_right h]
    unfold Tsup
    have := sup_factor_top (i := i) (j := j) ht
    nlinarith [this]

theorem sub_if_eq (ρ : ℝ) (t : ℕ) :
    (if t = 0 then (0 : ℝ) else Tsub ρ t) = Tsub ρ t := by
  by_cases h : t = 0
  · rw [ite_eq_left h, h]
    unfold Tsub
    simp
  · rw [ite_eq_right h]

theorem T_row_sum (t : Fin (min i j + 1)) :
    ∑ s, T i j θA θB ρ t s
      = (i : ℝ) * θA + (j : ℝ) * θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  have hlt : (t : ℕ) < min i j + 1 := t.isLt
  simp only [T_apply_eq_indicators, Finset.sum_add_distrib, sum_ite_val_eq, sum_ite_val_pred]
  rw [ite_eq_left hlt, sup_if_eq, sub_if_eq]
  unfold Tdiag Tsup Tsub slack
  ring

theorem T_offdiag_abs_sum (hρ : 0 ≤ ρ) (t : Fin (min i j + 1)) :
    ∑ s ∈ Finset.univ.erase t, |T i j θA θB ρ t s|
      = ρ * ((t : ℕ) : ℝ) + 2 * ((i : ℝ) - ((t : ℕ) : ℝ)) * ((j : ℝ) - ((t : ℕ) : ℝ)) := by
  have ht : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  have hti : ((t : ℕ) : ℝ) ≤ (i : ℝ) := by
    have : (t : ℕ) ≤ i := le_trans ht (min_le_left i j)
    exact_mod_cast this
  have htj : ((t : ℕ) : ℝ) ≤ (j : ℝ) := by
    have : (t : ℕ) ≤ j := le_trans ht (min_le_right i j)
    exact_mod_cast this
  have habs : ∀ s ∈ Finset.univ.erase t, |T i j θA θB ρ t s|
      = (if (s : ℕ) = (t : ℕ) + 1 then -Tsup i j (t : ℕ) else 0)
        + (if (t : ℕ) = (s : ℕ) + 1 then -Tsub ρ (t : ℕ) else 0) := by
    intro s hs
    have hne : (s : ℕ) ≠ (t : ℕ) := by
      have := (Finset.mem_erase.1 hs).1
      simpa [Fin.ext_iff] using this
    by_cases h2 : (s : ℕ) = (t : ℕ) + 1
    · have h3 : (t : ℕ) ≠ (s : ℕ) + 1 := by omega
      rw [T_apply_sup h2, ite_eq_left h2, ite_eq_right h3]
      unfold Tsup
      rw [abs_of_nonpos (by nlinarith)]
      ring
    · by_cases h3 : (t : ℕ) = (s : ℕ) + 1
      · rw [T_apply_sub h3, ite_eq_right h2, ite_eq_left h3]
        unfold Tsub
        rw [abs_of_nonpos (neg_nonpos.mpr (mul_nonneg hρ (Nat.cast_nonneg _)))]
        ring
      · rw [T_apply_zero hne h2 h3, ite_eq_right h2, ite_eq_right h3]
        simp
  rw [Finset.sum_congr rfl habs, Finset.sum_add_distrib]
  rw [Finset.sum_erase _ (by rw [ite_eq_right (by omega)]),
      Finset.sum_erase _ (by rw [ite_eq_right (by omega)])]
  rw [sum_ite_val_eq, sum_ite_val_pred]
  have h1 : (if (t : ℕ) + 1 < min i j + 1 then -Tsup i j (t : ℕ) else 0)
      = -Tsup i j (t : ℕ) := by
    by_cases h : (t : ℕ) + 1 < min i j + 1
    · rw [ite_eq_left h]
    · have hteq : (t : ℕ) = min i j := by omega
      rw [ite_eq_right h]
      unfold Tsup
      have := sup_factor_top (i := i) (j := j) hteq
      nlinarith [this]
  have h2 : (if (t : ℕ) = 0 then (0 : ℝ) else -Tsub ρ (t : ℕ)) = -Tsub ρ (t : ℕ) := by
    by_cases h : (t : ℕ) = 0
    · rw [ite_eq_left h, h]
      unfold Tsub
      simp
    · rw [ite_eq_right h]
  rw [h1, h2]
  unfold Tsup Tsub
  ring

theorem T_diag_sub_radius (hρ : 0 ≤ ρ) (t : Fin (min i j + 1)) :
    T i j θA θB ρ t t - ∑ s ∈ Finset.univ.erase t, |T i j θA θB ρ t s|
      = (i : ℝ) * θA + (j : ℝ) * θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  rw [T_apply_diag, T_offdiag_abs_sum hρ]
  unfold Tdiag slack
  ring

variable {lam : ℝ}

theorem Te_apply_diag (hlam : lam ≠ 0) (t : Fin (min i j + 1)) :
    Te i j lam θA θB ρ t t
      = ((i : ℝ) + (j : ℝ) - ((t : ℕ) : ℝ)) * ((i : ℝ) + (j : ℝ) - ((t : ℕ) : ℝ) - 1) / lam
        + (i : ℝ) * θA + (j : ℝ) * θB + ρ * ((t : ℕ) : ℝ) := by
  unfold Te
  rw [Matrix.smul_apply, smul_eq_mul, T_apply_diag]
  unfold Tdiag
  field_simp

theorem Te_apply_sup (hlam : lam ≠ 0) {t s : Fin (min i j + 1)} (h : (s : ℕ) = (t : ℕ) + 1) :
    Te i j lam θA θB ρ t s
      = -2 * ((i : ℝ) - ((t : ℕ) : ℝ)) * ((j : ℝ) - ((t : ℕ) : ℝ)) / lam := by
  unfold Te
  rw [Matrix.smul_apply, smul_eq_mul, T_apply_sup h]
  unfold Tsup
  field_simp

theorem Te_apply_sub (hlam : lam ≠ 0) {t s : Fin (min i j + 1)} (h : (t : ℕ) = (s : ℕ) + 1) :
    Te i j lam θA θB ρ t s = -(ρ * ((t : ℕ) : ℝ)) := by
  unfold Te
  rw [Matrix.smul_apply, smul_eq_mul, T_apply_sub h]
  unfold Tsub
  field_simp

end Rhone.LinearAlgebra.Spectral
