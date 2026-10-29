/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanPostPair
public import Rhone.Statistics.Identifiability.FirstExit

/-! # Eigenvectors and reward formulas for the three-sample pan generator -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false in
theorem flowOutput_eigenvector {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (a : ℝ) (hv : Q *ᵥ v = a • v)
    {t : ℝ} (ht : 0 ≤ t) : flowOutput Q i v 0 t = v i * Real.exp (a*t) := by
  have hd : ∀ x, 0 ≤ x → HasDerivAt (flowOutput Q i v 0)
      (-(-a)*flowOutput Q i v 0 x) x := by
    intro x _
    convert! flowOutput_hasDerivAt_right Q i v x using 1
    rw [hv]
    simp [flowOutput, Matrix.mulVec_smul]
  have h := survival_clock_of_forward_equation (flowOutput Q i v 0)
    (fun _ => -a) (fun x => -a*x) 0 hd
    (fun x _ => by convert! (hasDerivAt_id x).const_mul (-a) using 1; simp) ht
  simpa using h

noncomputable def panThreeGenerator : Matrix (Fin 2) (Fin 2) ℝ := !![-3,3;0,-1]
noncomputable def panThreeFast : Fin 2 → ℝ := ![1,0]
noncomputable def panThreeSlow : Fin 2 → ℝ := ![1,2/3]
noncomputable def panThreeSingletonReward : Fin 2 → ℝ := ![3,1]
noncomputable def panThreeDoubletonReward : Fin 2 → ℝ := ![0,1]

theorem panThree_eigenvectors :
    panThreeGenerator *ᵥ panThreeFast = (-3 : ℝ) • panThreeFast ∧
    panThreeGenerator *ᵥ panThreeSlow = (-1 : ℝ) • panThreeSlow := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [panThreeGenerator,panThreeFast,panThreeSlow,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem panThree_reward_decomposition :
    panThreeSingletonReward = (3/2 : ℝ) • (panThreeFast + panThreeSlow) ∧
    panThreeDoubletonReward = (3/2 : ℝ) • (panThreeSlow - panThreeFast) := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [panThreeSingletonReward,panThreeDoubletonReward,panThreeFast,panThreeSlow]

set_option backward.isDefEq.respectTransparency false in
theorem panThree_reward_formulas {t : ℝ} (ht : 0 ≤ t) :
    flowOutput panThreeGenerator 0 panThreeSingletonReward 0 t =
      (3/2 : ℝ)*(Real.exp (-t)+Real.exp (-3*t)) ∧
    flowOutput panThreeGenerator 0 panThreeDoubletonReward 0 t =
      (3/2 : ℝ)*(Real.exp (-t)-Real.exp (-3*t)) := by
  have hf := flowOutput_eigenvector panThreeGenerator 0 panThreeFast (-3)
    panThree_eigenvectors.1 ht
  have hs := flowOutput_eigenvector panThreeGenerator 0 panThreeSlow (-1)
    panThree_eigenvectors.2 ht
  simp only [panThreeFast,panThreeSlow,Matrix.cons_val_zero,one_mul,neg_mul,one_mul] at hf hs
  constructor
  · rw [panThree_reward_decomposition.1]
    simp only [flowOutput,Matrix.mulVec_smul,Matrix.mulVec_add,Pi.smul_apply,Pi.add_apply,
      smul_eq_mul, panThreeFast, panThreeSlow] at hf hs ⊢
    rw [hf,hs]
    simp only [neg_mul]
    ring
  · rw [panThree_reward_decomposition.2]
    simp only [flowOutput,Matrix.mulVec_smul,Matrix.mulVec_sub,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul, panThreeFast, panThreeSlow] at hf hs ⊢
    rw [hf,hs]
    simp only [neg_mul]

end Rhone.Statistics.Identifiability
