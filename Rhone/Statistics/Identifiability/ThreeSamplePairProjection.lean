/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeStateSemantics
public import Rhone.Statistics.Identifiability.ThreeLawSeparation

/-! # Five-state three-sample model projects to the pair model -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix Matrix.Norms.Operator
open MeasureTheory Set
namespace Rhone.Statistics.Identifiability

def threePairProjection : Matrix (Fin 5) (Fin 2) ℝ :=
  !![1, 0; 1/3, 2/3; 0, 1; 2/3, 0; 0, 2/3]

theorem three_pair_projection_generator (k : ℕ) (c q : ℝ) :
    islandThreeTreeGenerator k c q * threePairProjection =
      threePairProjection * MarkovChain.Identifiability.pairGenerator k c q := by
  ext i j
  change (∑ z : Fin 5, islandThreeTreeGenerator k c q i z * threePairProjection z j) =
    ∑ z : Fin 2, threePairProjection i z * MarkovChain.Identifiability.pairGenerator k c q z j
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator, threePairProjection,
        MarkovChain.Identifiability.pairGenerator,
      MarkovChain.Identifiability.totalMigration, Fin.sum_univ_succ] <;> ring

theorem three_pair_projection_reward :
    threePairProjection *ᵥ (fun _ => 1) =
      (1/3 : ℝ) • islandThreeFirstReward + (2/3 : ℝ) • (fun _ => 1) := by
  ext i
  fin_cases i <;>
    norm_num [threePairProjection, islandThreeFirstReward, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

def columnFunctional {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (Matrix.vecMul u M) j
      map_add' := by intro M N; simp [Matrix.vecMul_add]
      map_smul' := by intro a M; simp [Matrix.vecMul_smul] }

private theorem columnFunctional_apply {d : ℕ} (u : Fin d → ℝ) (j : Fin d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    columnFunctional u j M = (Matrix.vecMul u M) j := rfl

theorem matrix_exp_rectangular_intertwining {d e : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (R : Matrix (Fin e) (Fin e) ℝ)
    (H : Matrix (Fin d) (Fin e) ℝ) (h : Q * H = H * R) :
    NormedSpace.exp Q * H = H * NormedSpace.exp R := by
  have hp (n : ℕ) : Q ^ n * H = H * R ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  have h1 := (rowFunctional i (fun z => H z j)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Q)
  have h2 := (columnFunctional (H i) j).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) R)
  have hterm (n : ℕ) :
      rowFunctional i (fun z => H z j) ((n.factorial : ℝ)⁻¹ • Q ^ n) =
        columnFunctional (H i) j ((n.factorial : ℝ)⁻¹ • R ^ n) := by
    have he := congrFun (congrFun (hp n) i) j
    simp only [rowFunctional_apply, columnFunctional_apply, Matrix.mulVec,
      Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul]
    simp only [Matrix.mul_apply] at he
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [he]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have heq : (fun n : ℕ => rowFunctional i (fun z => H z j)
      ((n.factorial : ℝ)⁻¹ • Q ^ n)) =
      fun n : ℕ => columnFunctional (H i) j ((n.factorial : ℝ)⁻¹ • R ^ n) :=
    funext hterm
  rw [heq] at h1
  exact h1.unique h2

theorem three_pair_projection_exp (k : ℕ) (c q t : ℝ) :
    NormedSpace.exp (t • islandThreeTreeGenerator k c q) * threePairProjection =
      threePairProjection * NormedSpace.exp (t • MarkovChain.Identifiability.pairGenerator k c q) :=
          by
  apply matrix_exp_rectangular_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, three_pair_projection_generator]

theorem three_pair_survival_mixture (k : ℕ) (c q t : ℝ) :
    survivalJet k c q 0 t =
      (1/3 : ℝ) * flowOutput (islandThreeTreeGenerator k c q) 0
        islandThreeFirstReward 0 t +
      (2/3 : ℝ) * flowOutput (islandThreeTreeGenerator k c q) 0
        (fun _ => 1) 0 t := by
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 2) ℝ =>
    (M *ᵥ (fun _ => 1)) 0) (three_pair_projection_exp k c q t)
  rw [← Matrix.mulVec_mulVec, three_pair_projection_reward, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  have hright : (threePairProjection *ᵥ
      (NormedSpace.exp (t • MarkovChain.Identifiability.pairGenerator k c q) *ᵥ fun _ => 1)) 0 =
      survivalJet k c q 0 t := by
    simp [threePairProjection, survivalJet, flowOutput, MarkovChain.Identifiability.pairSurvival,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hright] at h
  simpa only [flowOutput, pow_zero, Matrix.one_mul] using h.symm

end Rhone.Statistics.Identifiability
