/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The block matrix at the inverse mutation parameter -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Matrix

variable {K : Type*} [Field K]

noncomputable def lambdaA : RatFunc K := RatFunc.X⁻¹
noncomputable def lambdaB (θ : K) : RatFunc K := RatFunc.C θ - RatFunc.X⁻¹

noncomputable def constantBlock (i j : ℕ) (θ ρ : K) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) (RatFunc K) :=
  (LinearAlgebra.Tridiag.T K i j 0 θ ρ).map RatFunc.C

theorem lambdaBlock_split (i j : ℕ) (θ ρ : K) :
    LinearAlgebra.Tridiag.T (RatFunc K) i j lambdaA (lambdaB θ) (RatFunc.C ρ) =
      (RatFunc.C ((i : K) - (j : K)) * RatFunc.X⁻¹) • 1 + constantBlock i j θ ρ := by
  rw [constantBlock, LinearAlgebra.Tridiag.T_map]
  simp only [map_zero]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl, LinearAlgebra.Tridiag.T_diag, LinearAlgebra.Tridiag.T_diag]
    simp only [lambdaA, lambdaB, map_sub, map_natCast]
    ring
  · have hv : (q : ℕ) ≠ (p : ℕ) := by
      intro he
      apply hpq
      exact Fin.ext he.symm
    simp only [ite_eq_right hpq, mul_zero, zero_add, LinearAlgebra.Tridiag.T_apply,
      LinearAlgebra.Tridiag.tridEntry, ite_eq_right hv]

theorem lambdaBlock_scaled (i j : ℕ) (θ ρ : K) :
    (RatFunc.X : RatFunc K) •
        LinearAlgebra.Tridiag.T (RatFunc K) i j lambdaA (lambdaB θ) (RatFunc.C ρ) =
      RatFunc.C ((i : K) - (j : K)) • 1 + (RatFunc.X : RatFunc K) • constantBlock i j θ ρ := by
  rw [lambdaBlock_split, smul_add, smul_smul]
  congr 1
  congr 1
  field_simp [RatFunc.X_ne_zero]

theorem lambdaBlock_diagonal (m : ℕ) (θ ρ : K) :
    LinearAlgebra.Tridiag.T (RatFunc K) m m lambdaA (lambdaB θ) (RatFunc.C ρ) =
      (LinearAlgebra.Tridiag.T K m m θ 0 ρ).map RatFunc.C := by
  rw [lambdaBlock_split]
  simp only [sub_self, map_zero, zero_mul, zero_smul, zero_add]
  unfold constantBlock
  congr 1
  ext p q
  simp only [LinearAlgebra.Tridiag.T_apply, LinearAlgebra.Tridiag.tridEntry,
      LinearAlgebra.Tridiag.dcoef]
  split_ifs <;> ring

theorem index_difference_ne_zero [CharZero K] {i j : ℕ} (hij : i ≠ j) :
    (i : K) - (j : K) ≠ 0 := by
  exact sub_ne_zero.mpr (by exact_mod_cast hij)

end Rhone.Algebra.SamplingUniform
