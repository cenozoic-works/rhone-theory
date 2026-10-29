/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExit
public import Rhone.Statistics.Identifiability.DifferentialDecay

/-! # A finite-dimensional Lyapunov certificate for eventual absorption -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Filter Set Finset
namespace Rhone.Statistics.Identifiability

theorem flowOutput_mono {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) {v w : Fin d → ℝ}
    (hvw : ∀ j, v j ≤ w j) {t : ℝ} (ht : 0 ≤ t) :
    flowOutput Q i v 0 t ≤ flowOutput Q i w 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j)
    (exp_generator_nonneg Q hQ ht i j)

theorem flowOutput_scale {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (a t : ℝ) :
    flowOutput Q i (fun j => a * v j) 0 t = a * flowOutput Q i v 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem survival_tendsto_zero_of_lyapunov {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (v : Fin d → ℝ) (hv : ∀ j, 1 ≤ v j)
    {a : ℝ} (ha : 0 < a) (hAv : ∀ j, (Q *ᵥ v) j ≤ -a) (i : Fin d) :
    Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0) := by
  let V : ℝ := 1 + ∑ j, v j
  have hv0 : ∀ j, 0 ≤ v j := fun j => le_trans zero_le_one (hv j)
  have hV : 0 < V := by
    have hs := sum_nonneg (fun j (_ : j ∈ Finset.univ) => hv0 j)
    dsimp [V]
    linarith
  have hjV : ∀ j, v j ≤ V := by
    intro j
    have h := single_le_sum (fun k (_ : k ∈ Finset.univ) => hv0 k) (Finset.mem_univ j)
    dsimp [V]
    linarith
  have he : 0 < a / V := div_pos ha hV
  have hbound : ∀ j, (Q *ᵥ v) j ≤ -(a / V) * v j := by
    intro j
    have h := mul_le_mul_of_nonneg_left (hjV j) he.le
    rw [div_mul_cancel₀ a hV.ne'] at h
    linarith [hAv j]
  have hdec : Tendsto (flowOutput Q i v 0) atTop (𝓝 0) :=
    tendsto_zero_of_exponential_decay _ _ he (flowOutput_hasDerivAt_right Q i v)
      (by
        intro t ht
        have h := flowOutput_mono Q hQ i (fun j => hv0 j) ht
        simpa [flowOutput, Matrix.mulVec, dotProduct] using h)
      (by
        intro t ht
        have h := flowOutput_mono Q hQ i hbound ht
        rwa [flowOutput_scale] at h)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdec
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_nonneg Q hQ i ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact flowOutput_mono Q hQ i hv ht

end Rhone.Statistics.Identifiability
