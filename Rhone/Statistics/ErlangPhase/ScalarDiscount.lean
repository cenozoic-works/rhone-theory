/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.Construction
public import Rhone.Statistics.Identifiability.RewardIntegral

/-! # Scalar-discount identities for flow output and survival in the Erlang-phase model -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Set Filter MeasureTheory
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability

theorem flowOutput_sub_scalar_identity {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (i : Fin d) (v : Fin d → ℝ) (t : ℝ) :
    flowOutput (Q - s • 1) i v 0 t = Real.exp (-s * t) * flowOutput Q i v 0 t := by
  have hsplit : t • (Q - s • 1) = (-s * t) • 1 + t • Q := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((-s * t) • (1 : Matrix (Fin d) (Fin d) ℝ)) (t • Q) :=
    (Commute.one_left _).smul_left _
  simp only [flowOutput, pow_zero, Matrix.one_mul]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_identity,
    Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]
  rfl

theorem isMetzler_sub_scalar_identity {d : Nat}
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsMetzler Q) (s : ℝ) :
    IsMetzler (Q - s • 1) := by
  intro i j hij
  simpa [Matrix.one_apply, hij] using hQ i j hij

theorem survival_sub_scalar_identity_tendsto_zero {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsMetzler Q)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin d)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    Tendsto (flowOutput (Q - s • 1) i (fun _ => 1) 0) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_nonneg _ (isMetzler_sub_scalar_identity hQ s) i ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [flowOutput_sub_scalar_identity]
    exact mul_le_of_le_one_left (survival_nonneg Q hQ i ht)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht))

end Rhone.Statistics.ErlangPhase
