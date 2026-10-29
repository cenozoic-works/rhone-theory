/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoIslandSpatial.Generators

/-! # Rectangular exponential intertwining for arbitrary finite spatial index types -/

@[expose] public section

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.TwoIslandSpatial

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def rowEval (i : α) (v : α → ℝ) : Matrix α α ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ v) i
      map_add' := by intro M N; simp [Matrix.add_mulVec]
      map_smul' := by intro a M; simp [Matrix.smul_mulVec] }

def columnEval (u : β → ℝ) (j : β) : Matrix β β ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (Matrix.vecMul u M) j
      map_add' := by intro M N; simp [Matrix.vecMul_add]
      map_smul' := by intro a M; simp [Matrix.vecMul_smul] }

lemma spatial_exp_intertwining (Q : Matrix α α ℝ) (R : Matrix β β ℝ)
    (H : Matrix α β ℝ) (h : Q * H = H * R) : NormedSpace.exp Q * H = H * NormedSpace.exp R := by
  have hp (n : ℕ) : Q^n*H = H * R^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  have h1 := (rowEval i (fun z => H z j)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Q)
  have h2 := (columnEval (H i) j).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) R)
  have hterm (n : ℕ) :
      rowEval i (fun z => H z j) ((n.factorial : ℝ)⁻¹ • Q^n) =
        columnEval (H i) j ((n.factorial : ℝ)⁻¹ • R^n) := by
    have he := congrFun (congrFun (hp n) i) j
    change (((n.factorial : ℝ)⁻¹ • Q^n) *ᵥ (fun z => H z j)) i =
      (Matrix.vecMul (H i) ((n.factorial : ℝ)⁻¹ • R^n)) j
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul]
    simp only [Matrix.mul_apply] at he
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [he]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have heq : (fun n : ℕ => rowEval i (fun z => H z j) ((n.factorial : ℝ)⁻¹ • Q^n)) =
      fun n : ℕ => columnEval (H i) j ((n.factorial : ℝ)⁻¹ • R^n) := funext hterm
  rw [heq] at h1
  exact h1.unique h2

end Rhone.Statistics.TwoIslandSpatial
