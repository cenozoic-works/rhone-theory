/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExitLaw

/-! # Finite Markov reward potentials identify expected occupation rewards -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Set Filter MeasureTheory Finset
namespace Rhone.Statistics.Identifiability

theorem flowOutput_tendsto_zero {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) (v : Fin d → ℝ)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    Tendsto (flowOutput Q i v 0) atTop (𝓝 0) := by
  let C : ℝ := ∑ j, |v j|
  have hb : ∀ j, |v j| ≤ C := fun j =>
    single_le_sum (fun z (_ : z ∈ Finset.univ) => abs_nonneg (v z)) (Finset.mem_univ j)
  have hl : Tendsto (fun t => -C * flowOutput Q i (fun _ => 1) 0 t) atTop (𝓝 0) := by
    simpa using htail.const_mul (-C)
  have hu : Tendsto (fun t => C * flowOutput Q i (fun _ => 1) 0 t) atTop (𝓝 0) := by
    simpa using htail.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hv : ∀ j, -C * (1 : ℝ) ≤ v j := by
      intro j
      have hh := (abs_le.mp (hb j)).1
      simpa using hh
    have h := flowOutput_mono Q hQ i hv ht
    rwa [flowOutput_scale] at h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hv : ∀ j, v j ≤ C * (1 : ℝ) := by
      intro j
      simpa using (abs_le.mp (hb j)).2
    have h := flowOutput_mono Q hQ i hv ht
    rwa [flowOutput_scale] at h

set_option backward.isDefEq.respectTransparency false in
theorem reward_potential_derivative {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (u reward : Fin d → ℝ) (hu : Q *ᵥ u = -reward) (t : ℝ) :
    HasDerivAt (fun x => -flowOutput Q i u 0 x) (flowOutput Q i reward 0 t) t := by
  have h := (flowOutput_hasDerivAt_right Q i u t).neg
  rw [hu] at h
  convert! h using 1
  first | rfl | simp [flowOutput, Matrix.mulVec_neg]

theorem reward_integrable {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) (u reward : Fin d → ℝ)
    (hu : Q *ᵥ u = -reward) (hr : ∀ j, 0 ≤ reward j)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    IntegrableOn (flowOutput Q i reward 0) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (fun t _ => reward_potential_derivative Q i u reward hu t)
  · intro t ht
    simp only [flowOutput, pow_zero, Matrix.one_mul]
    exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg Q hQ ht.le) hr i
  · simpa using (flowOutput_tendsto_zero Q hQ i u htail).neg

theorem reward_integral_eq_potential {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (i : Fin d) (u reward : Fin d → ℝ)
    (hu : Q *ᵥ u = -reward) (hr : ∀ j, 0 ≤ reward j)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    (∫ t in Ioi 0, flowOutput Q i reward 0 t) = u i := by
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ flowOutput Q i reward 0 t := by
    intro t ht
    simp only [flowOutput, pow_zero, Matrix.one_mul]
    exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg Q hQ ht.le) hr i
  have htail' : Tendsto (fun t => -flowOutput Q i u 0 t) atTop (𝓝 0) := by
    simpa using (flowOutput_tendsto_zero Q hQ i u htail).neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => reward_potential_derivative Q i u reward hu t) hpos htail'
  simpa using h

end Rhone.Statistics.Identifiability
