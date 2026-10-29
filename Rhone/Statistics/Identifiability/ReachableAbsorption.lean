/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Absorption
public import Rhone.Statistics.Identifiability.Admissibility

/-! # Lyapunov absorption restricted to an invariant set of admissible states -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Filter Finset
namespace Rhone.Statistics.Identifiability

theorem flowOutput_mono_on {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (P : Fin d → Prop)
    (hP : ∀ i j, P i → ¬ P j → Q i j = 0) (i : Fin d) (hi : P i)
    {v w : Fin d → ℝ} (hvw : ∀ j, P j → v j ≤ w j) {t : ℝ} (ht : 0 ≤ t) :
    flowOutput Q i v 0 t ≤ flowOutput Q i w 0 t := by
  classical
  simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  apply sum_le_sum
  intro j _
  by_cases hj : P j
  · exact mul_le_mul_of_nonneg_left (hvw j hj) (exp_generator_nonneg Q hQ ht i j)
  · rw [matrix_exp_no_escape Q P hP t i j hi hj, zero_mul, zero_mul]

theorem survival_tendsto_zero_of_reachable_lyapunov {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsMetzler Q) (P : Fin d → Prop)
    (hP : ∀ i j, P i → ¬ P j → Q i j = 0)
    (v : Fin d → ℝ) (hv : ∀ j, 1 ≤ v j)
    {a : ℝ} (ha : 0 < a) (hAv : ∀ j, P j → (Q *ᵥ v) j ≤ -a)
    (i : Fin d) (hi : P i) :
    Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0) := by
  let V : ℝ := 1 + ∑ j, v j
  have hv0 : ∀ j, 0 ≤ v j := fun j => le_trans zero_le_one (hv j)
  have hV : 0 < V := by
    have hs := sum_nonneg (fun j (_ : j ∈ Finset.univ) => hv0 j)
    dsimp [V]
    linarith
  have hjV : ∀ j, v j ≤ V := by
    intro j
    have h := single_le_sum (fun k (_ : k ∈ Finset.univ) => hv0 k) (mem_univ j)
    dsimp [V]
    linarith
  have he : 0 < a / V := div_pos ha hV
  have hbound : ∀ j, P j → (Q *ᵥ v) j ≤ -(a / V) * v j := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hjV j) he.le
    rw [div_mul_cancel₀ a hV.ne'] at h
    linarith [hAv j hj]
  have hdec : Tendsto (flowOutput Q i v 0) atTop (𝓝 0) :=
    tendsto_zero_of_exponential_decay _ _ he (flowOutput_hasDerivAt_right Q i v)
      (by
        intro t ht
        have h := flowOutput_mono Q hQ i (fun j => hv0 j) ht
        simpa [flowOutput, Matrix.mulVec, dotProduct] using h)
      (by
        intro t ht
        have h := flowOutput_mono_on Q hQ P hP i hi hbound ht
        rwa [flowOutput_scale] at h)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdec
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_nonneg Q hQ i ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact flowOutput_mono Q hQ i hv ht

end Rhone.Statistics.Identifiability
