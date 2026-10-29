/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CTMC

/-! # Scalar series for a matrix-exponential output at arbitrary time -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false in
theorem flowOutput_series {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (t : ℝ) :
    HasSum (fun n : Nat => (n.factorial : ℝ)⁻¹ * t^n * (Q^n *ᵥ v) i)
      (flowOutput Q i v 0 t) := by
  have h := (rowFunctional i v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q))
  simp only [map_smul, rowFunctional_apply, smul_pow, smul_eq_mul] at h
  convert! h using 1
  · funext n
    ring
  · simp [flowOutput]

end Rhone.Statistics.Identifiability
