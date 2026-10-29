/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.NoRecombinationOverlap
public import Mathlib.Tactic

/-! # Finite pruned two-site ARG kernels and pure-coalescence pulse convergence -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

abbrev State := Fin 5

def C : Matrix State State ℝ :=
  !![-1, 0, 0, 0, 1;
      1, -3, 0, 2, 0;
      0, 4, -6, 2, 0;
      0, 0, 0, -1, 1;
      0, 0, 0, 0, 0]

def R : Matrix State State ℝ :=
  !![-2, 2, 0, 0, 0;
      0, -1, 1, 0, 0;
      0, 0, 0, 0, 0;
      0, 0, 0, 0, 0;
      0, 0, 0, 0, 0]

def d : State → ℝ := ![2, 2, 2, 1, 0]

def D : Matrix State State ℝ := Matrix.diagonal d

def G (lam r : ℝ) : Matrix State State ℝ := lam • C + r • R

def B (lam r k : ℝ) : Matrix State State ℝ := G lam r - k • D

theorem C_metzler : IsMetzler C := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [C] at *

theorem R_metzler : IsMetzler R := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [R] at *

theorem C_conservative : IsConservative C := by
  ext i
  fin_cases i <;> norm_num [C, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem R_conservative : IsConservative R := by
  ext i
  fin_cases i <;> norm_num [R, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem d_nonneg (i : State) : 0 ≤ d i := by
  fin_cases i <;> norm_num [d]

theorem d_le_two (i : State) : d i ≤ 2 := by
  fin_cases i <;> norm_num [d]

theorem D_nonneg (i j : State) : 0 ≤ D i j := by
  by_cases hij : i = j
  · subst j; simpa [D] using d_nonneg i
  · simp [D, Matrix.diagonal_apply_ne _ hij]

theorem G_metzler {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) :
    IsMetzler (G lam r) := by
  intro i j hij
  exact add_nonneg (mul_nonneg hlam (C_metzler i j hij))
    (mul_nonneg hr (R_metzler i j hij))

theorem G_conservative (lam r : ℝ) : IsConservative (G lam r) := by
  dsimp [IsConservative, G]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    C_conservative, R_conservative, smul_zero, smul_zero, add_zero]

theorem B_metzler {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) (k : ℝ) :
    IsMetzler (B lam r k) := by
  intro i j hij
  simpa [B, D, Matrix.diagonal_apply_ne _ hij] using G_metzler hlam hr i j hij

theorem B_row_sums (lam r k : ℝ) : B lam r k *ᵥ (fun _ => 1) = -k • d := by
  dsimp [B, D]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, G_conservative]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem B_le_G {k : ℝ} (hk : 0 ≤ k) (lam r : ℝ) (i j : State) :
    B lam r k i j ≤ G lam r i j := by
  exact sub_le_self _ (mul_nonneg hk (D_nonneg i j))

theorem exp_B_nonneg {lam r k t : ℝ}
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ∀ i j, 0 ≤ NormedSpace.exp (t • B lam r k) i j :=
  exp_generator_nonneg _ (B_metzler hlam hr k) ht

theorem exp_B_row_le_one {lam r k t : ℝ}
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k) (ht : 0 ≤ t) (i : State) :
    (NormedSpace.exp (t • B lam r k) *ᵥ (fun _ => 1)) i ≤ 1 := by
  have hmono := matrix_exp_mono_of_metzler (B_metzler hlam hr k) (B_le_G hk lam r) ht
  have hrow := congrFun (exp_generator_rows (G lam r) (G_conservative lam r) t) i
  calc
    _ ≤ (NormedSpace.exp (t • G lam r) *ᵥ (fun _ => 1)) i := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hmono i j) zero_le_one
    _ = 1 := hrow

theorem exp_B_substochastic {lam r k t : ℝ}
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    (∀ i j, 0 ≤ NormedSpace.exp (t • B lam r k) i j) ∧
    (∀ i, (NormedSpace.exp (t • B lam r k) *ᵥ (fun _ => 1)) i ≤ 1) :=
  ⟨exp_B_nonneg hlam hr ht, exp_B_row_le_one hlam hr hk ht⟩

theorem exp_B_norm_le_one {lam r k t : ℝ}
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • B lam r k)‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  have hn := exp_B_nonneg (k := k) hlam hr ht
  suffices h : (Finset.univ.sup fun i : State =>
      ∑ j : State, ‖NormedSpace.exp (t • B lam r k) i j‖₊) ≤ 1 by
    exact_mod_cast h
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (hn i _), Matrix.mulVec, dotProduct, mul_one] using
      exp_B_row_le_one hlam hr hk ht i

theorem exp_B_mulVec_norm_le {lam r k t : ℝ}
    (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k) (ht : 0 ≤ t)
    (v : State → ℝ) :
    ‖NormedSpace.exp (t • B lam r k) *ᵥ v‖ ≤ ‖v‖ := by
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (by simpa using (mul_le_mul_of_nonneg_right
      (exp_B_norm_le_one hlam hr hk ht) (norm_nonneg v)))

theorem B_absorbing_row (lam r k : ℝ) (j : State) : B lam r k 4 j = 0 := by
  change B lam r k (⟨4, by decide⟩ : Fin 5) j = 0
  fin_cases j <;> norm_num [B, G, C, R, D, d, Matrix.diagonal_apply]

theorem C_norm : ‖C‖ = 12 := by
  have hu : (Finset.univ : Finset State) = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by
    decide⟩, ⟨4, by decide⟩} := by decide
  rw [Matrix.linfty_opNorm_def, hu]
  norm_num [C, State, Finset.sum_insert, Finset.sum_singleton]

theorem R_norm : ‖R‖ = 4 := by
  have hu : (Finset.univ : Finset State) = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by
    decide⟩, ⟨4, by decide⟩} := by decide
  rw [Matrix.linfty_opNorm_def, hu]
  norm_num [R, State, Finset.sum_insert, Finset.sum_singleton]

theorem D_norm : ‖D‖ = 2 := by
  have hu : (Finset.univ : Finset State) = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by
    decide⟩, ⟨4, by decide⟩} := by decide
  rw [Matrix.linfty_opNorm_def, hu]
  norm_num [D, d, State, Matrix.diagonal_apply, Finset.sum_insert, Finset.sum_singleton]

theorem C_mul_d : C *ᵥ d = (-1 : ℝ) • d := by
  ext i
  fin_cases i <;> norm_num [C, d, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pow_mulVec_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (a : ℝ) (hv : A *ᵥ v = a • v) (m : ℕ) :
    A ^ m *ᵥ v = a ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv,
      smul_smul, pow_succ]

theorem exp_mulVec_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (a : ℝ) (hv : A *ᵥ v = a • v) :
    NormedSpace.exp A *ᵥ v = Real.exp a • v := by
  ext i
  have hs := (rowFunctional i v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A)
  have hs' := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).mul_right (v i)
  simp only [map_smul, rowFunctional_apply, pow_mulVec_eigen A v a hv,
    Pi.smul_apply, smul_eq_mul] at hs
  simp only [smul_eq_mul, ← Real.exp_eq_exp_ℝ, mul_assoc] at hs'
  simpa only [Pi.smul_apply, smul_eq_mul] using hs.unique hs'

theorem exp_zero_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (hi : ∀ j, A i j = 0) (j : Fin n) :
    NormedSpace.exp A i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have hev : Aᵀ *ᵥ Pi.single i 1 = (0 : ℝ) • Pi.single i 1 := by
    ext k
    simp [hi]
  have h := congrFun (exp_mulVec_eigen Aᵀ (Pi.single i 1) 0 hev) j
  by_cases hij : i = j
  · subst j; simpa [Matrix.exp_transpose] using h
  · simpa [Matrix.exp_transpose, Matrix.transpose_apply, Matrix.one_apply,
      Pi.single_apply, hij, Ne.symm hij] using h

theorem exp_B_absorbing_row (lam r k t : ℝ) (j : State) :
    NormedSpace.exp (t • B lam r k) 4 j = (1 : Matrix State State ℝ) 4 j := by
  apply exp_zero_row
  intro j
  simp [B_absorbing_row]

theorem exp_C_mul_d (t : ℝ) :
    NormedSpace.exp (t • C) *ᵥ d = Real.exp (-t) • d := by
  apply exp_mulVec_eigen
  rw [Matrix.smul_mulVec, C_mul_d, smul_smul]
  simp

theorem mulVec_mono {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) {v w : Fin n → ℝ} (hvw : ∀ i, v i ≤ w i) :
    ∀ i, (A *ᵥ v) i ≤ (A *ᵥ w) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j) (hA i j)

theorem deficit_bounds (v : State → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1) :
    (∀ i, 0 ≤ 1 - v i) ∧ (∀ i, 1 - v i ≤ d i) := by
  refine ⟨fun i => sub_nonneg.mpr (hv1 i), ?_⟩
  intro i
  have hi := hv0 i
  by_cases ha : i = 4
  · subst i; simpa only [hvabs, sub_self] using d_nonneg 4
  · have hd : 1 ≤ d i := by
      fin_cases i <;> norm_num [d] at *
    linarith

theorem pure_pulse_deficit_bound (v : State → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1) {t : ℝ} (ht : 0 ≤ t)
    (i : State) :
    0 ≤ 1 - (NormedSpace.exp (t • C) *ᵥ v) i ∧
    1 - (NormedSpace.exp (t • C) *ᵥ v) i ≤ Real.exp (-t) * d i := by
  have hpos := exp_generator_nonneg C C_metzler ht
  have hrow := exp_generator_rows C C_conservative t
  have heq : NormedSpace.exp (t • C) *ᵥ (fun j => 1 - v j) =
      (fun j => 1 - (NormedSpace.exp (t • C) *ᵥ v) j) := by
    change NormedSpace.exp (t • C) *ᵥ ((fun _ => 1) - v) = _
    rw [Matrix.mulVec_sub, hrow]
    rfl
  obtain ⟨hdef0, hdefd⟩ := deficit_bounds v hv0 hv1 hvabs
  have hlow := matrix_mulVec_nonneg _ _ hpos hdef0 i
  have hupp := mulVec_mono _ hpos hdefd i
  rw [heq] at hlow hupp
  rw [exp_C_mul_d] at hupp
  exact ⟨hlow, hupp⟩

theorem pure_pulse_norm_bound (v : State → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • C) *ᵥ v - (fun _ => 1)‖ ≤ 2 * Real.exp (-t) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  obtain ⟨hlow, hupp⟩ := pure_pulse_deficit_bound v hv0 hv1 hvabs ht i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_sub_comm, abs_of_nonneg hlow]
  calc
    _ ≤ Real.exp (-t) * d i := hupp
    _ ≤ Real.exp (-t) * 2 := mul_le_mul_of_nonneg_left (d_le_two i) (Real.exp_pos _).le
    _ = 2 * Real.exp (-t) := mul_comm _ _

end Rhone.Statistics.Identifiability.MutationPulseKernel
