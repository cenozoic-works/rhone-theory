/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Derivatives of finite matrix-exponential observables -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability

noncomputable def rowFunctional {d : Nat} (i : Fin d) (v : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ v) i
      map_add' := by intro M N; simp [Matrix.add_mulVec]
      map_smul' := by intro a M; simp [Matrix.smul_mulVec] }

@[simp] theorem rowFunctional_apply {d : Nat} (i : Fin d) (v : Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    rowFunctional i v M = (M *ᵥ v) i := rfl

noncomputable def flowOutput {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) (t : ℝ) : ℝ :=
  ((Q ^ k * NormedSpace.exp (t • Q)) *ᵥ v) i

set_option backward.isDefEq.respectTransparency false in
theorem flowOutput_hasDerivAt {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) (t : ℝ) :
    HasDerivAt (flowOutput Q i v k) (flowOutput Q i v (k+1) t) t := by
  have h := (hasDerivAt_exp_smul_const' Q t).const_mul (Q ^ k)
  have hh := (rowFunctional i v).hasFDerivAt.comp_hasDerivAt t h
  convert! hh using 1
  simp [flowOutput, pow_succ, mul_assoc]

@[simp] theorem flowOutput_zero {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) :
    flowOutput Q i v k 0 = (Q ^ k *ᵥ v) i := by
  simp [flowOutput]

theorem flowOutput_continuous {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) :
    Continuous (flowOutput Q i v k) :=
  continuous_iff_continuousAt.mpr fun t =>
    (flowOutput_hasDerivAt Q i v k t).continuousAt

@[simp] theorem flowOutput_initial {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) :
    flowOutput Q i v 0 0 = v i := by
  simp

end Rhone.Statistics.Identifiability
