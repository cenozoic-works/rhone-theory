/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseKernel

/-! # Exact transforms for the ideal pure-coalescence pulse followed by a zero-coalescence epoch -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationIdealTransform
open MutationPulseKernel

local notation "State" => Fin 5
local notation "s3" => (⟨3, by decide⟩ : State)
local notation "s4" => (⟨4, by decide⟩ : State)

def twoUnresolved : State → ℝ := ![1, 1, 1, 0, 0]

def oneUnresolved : State → ℝ := ![0, 0, 0, 1, 0]

def absorbed : State → ℝ := ![0, 0, 0, 0, 1]

theorem ones_decomposition :
    (fun _ : State => (1 : ℝ)) = twoUnresolved + oneUnresolved + absorbed := by
  ext i
  fin_cases i <;> norm_num [twoUnresolved, oneUnresolved, absorbed]

theorem B_zero_twoUnresolved (r k : ℝ) :
    B 0 r k *ᵥ twoUnresolved = (-2 * k) • twoUnresolved := by
  ext i
  fin_cases i <;>
    simp [B, G, R, D, d, twoUnresolved, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply] <;> ring

theorem B_zero_oneUnresolved (r k : ℝ) :
    B 0 r k *ᵥ oneUnresolved = (-k) • oneUnresolved := by
  ext i
  fin_cases i <;>
    simp [B, G, R, D, d, oneUnresolved, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem B_zero_absorbed (r k : ℝ) :
    B 0 r k *ᵥ absorbed = 0 := by
  ext i
  fin_cases i <;>
    simp [B, G, R, D, d, absorbed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem exp_B_zero_ones (τ r k : ℝ) :
    NormedSpace.exp (τ • B 0 r k) *ᵥ (fun _ => 1) =
      Real.exp (-2 * k * τ) • twoUnresolved +
      Real.exp (-k * τ) • oneUnresolved + absorbed := by
  have htwo : NormedSpace.exp (τ • B 0 r k) *ᵥ twoUnresolved =
      Real.exp (-2 * k * τ) • twoUnresolved := by
    apply exp_mulVec_eigen
    rw [Matrix.smul_mulVec, B_zero_twoUnresolved, smul_smul]
    congr 1
    ring
  have hone : NormedSpace.exp (τ • B 0 r k) *ᵥ oneUnresolved =
      Real.exp (-k * τ) • oneUnresolved := by
    apply exp_mulVec_eigen
    rw [Matrix.smul_mulVec, B_zero_oneUnresolved, smul_smul]
    congr 1
    ring
  have habs : NormedSpace.exp (τ • B 0 r k) *ᵥ absorbed = absorbed := by
    have he : (τ • B 0 r k) *ᵥ absorbed = (0 : ℝ) • absorbed := by
      rw [Matrix.smul_mulVec, B_zero_absorbed, smul_zero, zero_smul]
    simpa using exp_mulVec_eigen (τ • B 0 r k) absorbed 0 he
  rw [ones_decomposition, Matrix.mulVec_add, Matrix.mulVec_add, htwo, hone, habs]

theorem exp_C_absorbing_row (A : ℝ) (j : State) :
    NormedSpace.exp (A • C) s4 j = (1 : Matrix State State ℝ) s4 j := by
  apply exp_zero_row
  intro l
  fin_cases l <;> norm_num [C, Matrix.cons_val_four]

theorem exp_C_row (A : ℝ) (i : State) (hi : i = 0 ∨ i = s3) (j : State) :
    NormedSpace.exp (A • C) i j =
      Real.exp (-A) * (1 : Matrix State State ℝ) i j +
      (1 - Real.exp (-A)) * (1 : Matrix State State ℝ) s4 j := by
  let v : State → ℝ := Pi.single i 1 - Pi.single s4 1
  have he : (A • C)ᵀ *ᵥ v = (-A) • v := by
    rcases hi with rfl | rfl
    · ext l
      fin_cases l <;>
        norm_num [v, C, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          Pi.single_apply, Matrix.transpose_apply]
    · ext l
      fin_cases l <;>
        norm_num [v, C, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
          Pi.single_apply, Matrix.transpose_apply]
  have hs := congrFun (exp_mulVec_eigen (A • C)ᵀ v (-A) he) j
  rw [Matrix.exp_transpose] at hs
  have hs' : NormedSpace.exp (A • C) i j - NormedSpace.exp (A • C) s4 j =
      Real.exp (-A) * ((Pi.single i (1 : ℝ) : State → ℝ) j - (Pi.single (s4 : State) (1 : ℝ) :
        State → ℝ) j) := by
    simpa [v, Matrix.mulVec_sub] using hs
  rw [exp_C_absorbing_row] at hs'
  have hi' : (Pi.single i (1 : ℝ) : State → ℝ) j = (1 : Matrix State State ℝ) i j := by
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have ha' : (Pi.single (s4 : State) (1 : ℝ) : State → ℝ) j = (1 : Matrix State State ℝ) s4 j :=
    by
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [hi', ha'] at hs'
  linarith

theorem exp_C_mulVec_at (A : ℝ) (v : State → ℝ) (i : State)
    (hi : i = 0 ∨ i = s3) :
    (NormedSpace.exp (A • C) *ᵥ v) i =
      Real.exp (-A) * v i + (1 - Real.exp (-A)) * v s4 := by
  calc
    _ = Real.exp (-A) * ((1 : Matrix State State ℝ) *ᵥ v) i +
        (1 - Real.exp (-A)) * ((1 : Matrix State State ℝ) *ᵥ v) s4 := by
      simp only [Matrix.mulVec, dotProduct, exp_C_row A i hi, add_mul,
        Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    _ = _ := by rw [Matrix.one_mulVec]

theorem ideal_two_locus_transform (A τ r k : ℝ) :
    (NormedSpace.exp (A • C) *ᵥ
      (NormedSpace.exp (τ • B 0 r k) *ᵥ (fun _ => 1))) 0 =
      1 - Real.exp (-A) + Real.exp (-A) * Real.exp (-2 * k * τ) := by
  rw [exp_C_mulVec_at A _ 0 (Or.inl rfl), exp_B_zero_ones]
  norm_num [twoUnresolved, oneUnresolved, absorbed, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

theorem ideal_one_locus_transform (A τ r k : ℝ) :
    (NormedSpace.exp (A • C) *ᵥ
      (NormedSpace.exp (τ • B 0 r k) *ᵥ (fun _ => 1))) s3 =
      1 - Real.exp (-A) + Real.exp (-A) * Real.exp (-k * τ) := by
  rw [exp_C_mulVec_at A _ s3 (Or.inr rfl), exp_B_zero_ones]
  norm_num [twoUnresolved, oneUnresolved, absorbed, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

end Rhone.Statistics.Identifiability.MutationIdealTransform
