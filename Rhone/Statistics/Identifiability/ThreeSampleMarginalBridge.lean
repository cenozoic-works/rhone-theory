/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplePairProjection

/-! # Projection of the three-sample island generator onto the first-merger marginal -/

@[expose] public section

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

def threeFirstProjection : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0]

theorem three_first_projection_generator (k : ℕ) (c q : ℝ) :
    islandThreeTreeGenerator k c q * threeFirstProjection =
      threeFirstProjection * threeGenerator k c q := by
  ext i j
  change (∑ z : Fin 5, islandThreeTreeGenerator k c q i z * threeFirstProjection z j) =
    ∑ z : Fin 3, threeFirstProjection i z * threeGenerator k c q z j
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator, threeFirstProjection, threeGenerator,
      MarkovChain.Identifiability.totalMigration, Fin.sum_univ_succ] <;> ring

theorem three_first_projection_reward :
    threeFirstProjection *ᵥ (fun _ => 1) = islandThreeFirstReward := by
  ext i
  fin_cases i <;>
    norm_num [threeFirstProjection, islandThreeFirstReward, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

theorem three_first_projection_exp (k : ℕ) (c q t : ℝ) :
    NormedSpace.exp (t • islandThreeTreeGenerator k c q) * threeFirstProjection =
      threeFirstProjection * NormedSpace.exp (t • threeGenerator k c q) := by
  apply matrix_exp_rectangular_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, three_first_projection_generator]

theorem three_first_survival_from_full_generator (k : ℕ) (c q t : ℝ) :
    flowOutput (islandThreeTreeGenerator k c q) 0 islandThreeFirstReward 0 t =
      threeSurvivalJet k c q 0 t := by
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 3) ℝ =>
    (M *ᵥ (fun _ => 1)) 0) (three_first_projection_exp k c q t)
  rw [← Matrix.mulVec_mulVec, three_first_projection_reward,
    ← Matrix.mulVec_mulVec] at h
  have hright : (threeFirstProjection *ᵥ
      (NormedSpace.exp (t • threeGenerator k c q) *ᵥ fun _ => 1)) 0 =
      threeSurvivalJet k c q 0 t := by
    simp [threeFirstProjection, threeSurvivalJet, flowOutput,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hright] at h
  simpa only [flowOutput, pow_zero, Matrix.one_mul] using h

theorem island_pair_first_root_survival_identity (k : ℕ) (c q t : ℝ) :
    survivalJet k c q 0 t = (1/3 : ℝ) * threeSurvivalJet k c q 0 t +
      (2/3 : ℝ) * flowOutput (islandThreeTreeGenerator k c q) 0 (fun _ => 1) 0 t := by
  rw [three_pair_survival_mixture, three_first_survival_from_full_generator]

end Rhone.Statistics.Identifiability
