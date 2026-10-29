/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeGenerator
public import Rhone.Statistics.Identifiability.ThreeSpectrumOverlap
public import Rhone.Statistics.Identifiability.RewardIntegral

/-! # Three-sample island spectrum and its exact panmictic mimic -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def islandThreeTreeGenerator (k : ℕ) (c q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-3*c-3*((k:ℝ)+1)*q, 3*((k:ℝ)+1)*q, 0, 3*c, 0;
     q, -c-(2*(k:ℝ)+1)*q, 2*(k:ℝ)*q, 0, c;
     0, 6*q, -6*q, 0, 0;
     0, 0, 0, -c-2*((k:ℝ)+1)*q, 2*((k:ℝ)+1)*q;
     0, 0, 0, 2*q, -2*q]

noncomputable def islandThreeFirstMean (k : ℕ) (c q : ℝ) : ℝ :=
  (c+((k:ℝ)+2)^2*q)/(3*c*(c+((k:ℝ)+2)*q))
noncomputable def islandThreeDoubleMean (k : ℕ) (c q : ℝ) : ℝ :=
  ((3*((k:ℝ)+2)-1)*c+2*((k:ℝ)+2)^2*q)/(2*c*(c+((k:ℝ)+2)*q))
noncomputable def islandThreeFirstPotential (k : ℕ) (c q : ℝ) : Fin 5 → ℝ :=
  ![islandThreeFirstMean k c q,
    (((k:ℝ)+3)*c+((k:ℝ)+2)^2*q)/(3*c*(c+((k:ℝ)+2)*q)),
    (((k:ℝ)+3)*c+((k:ℝ)+2)^2*q)/(3*c*(c+((k:ℝ)+2)*q))+1/(6*q),0,0]
noncomputable def islandThreeDoublePotential (k : ℕ) (c q : ℝ) : Fin 5 → ℝ :=
  ![islandThreeDoubleMean k c q,
    islandThreeDoubleMean k c q+c/(2*q*(c+((k:ℝ)+2)*q)),
    islandThreeDoubleMean k c q+c/(2*q*(c+((k:ℝ)+2)*q)),
    ((k:ℝ)+2)/c,((k:ℝ)+2)/c+1/(2*q)]
noncomputable def islandThreeFirstReward : Fin 5 → ℝ := ![1,1,1,0,0]
noncomputable def islandThreeDoubleReward : Fin 5 → ℝ := ![0,0,0,1,1]
noncomputable def islandThreeSingleReward : Fin 5 → ℝ := ![3,3,3,1,1]

theorem islandThreeTree_metzler (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    IsMetzler (islandThreeTreeGenerator k c q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator] at * <;> positivity

theorem islandThreeTree_rows_nonpos (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (i : Fin 5) :
    (∑ j, islandThreeTreeGenerator k c q i j) ≤ 0 := by
  fin_cases i <;> simp [islandThreeTreeGenerator,Fin.sum_univ_succ] <;> linarith

theorem islandThree_potential_drifts (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    islandThreeTreeGenerator k c q *ᵥ islandThreeFirstPotential k c q = -islandThreeFirstReward ∧
    islandThreeTreeGenerator k c q *ᵥ islandThreeDoublePotential k c q =
      -islandThreeDoubleReward := by
  have hd : c+((k:ℝ)+2)*q ≠ 0 := ne_of_gt (by positivity : 0 < c+((k:ℝ)+2)*q)
  constructor <;> ext i <;> fin_cases i <;>
    simp [islandThreeTreeGenerator,islandThreeFirstPotential,islandThreeDoublePotential,
      islandThreeFirstMean,islandThreeDoubleMean,islandThreeFirstReward,islandThreeDoubleReward,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem islandThree_means_positive (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    0 < islandThreeFirstMean k c q ∧ 0 < islandThreeDoubleMean k c q := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · unfold islandThreeFirstMean
    positivity
  · unfold islandThreeDoubleMean
    have h : 0 < 3*((k:ℝ)+2)-1 := by linarith
    positivity

theorem islandThree_potentials_nonneg (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (i : Fin 5) : 0 ≤ islandThreeFirstPotential k c q i ∧
      0 ≤ islandThreeDoublePotential k c q i := by
  have ha := (islandThree_means_positive k hc hq).1
  have hb := (islandThree_means_positive k hc hq).2
  constructor <;> fin_cases i <;>
    norm_num [islandThreeFirstPotential,islandThreeDoublePotential] <;> positivity

theorem islandThree_survival_tendsto_zero (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (i : Fin 5) : Tendsto (flowOutput (islandThreeTreeGenerator k c q) i (fun _ => 1) 0)
      atTop (𝓝 0) := by
  let v : Fin 5 → ℝ := fun j => 1 + islandThreeFirstPotential k c q j +
    islandThreeDoublePotential k c q j
  have hv : ∀ j, 1 ≤ v j := by
    intro j
    have h := islandThree_potentials_nonneg k hc hq j
    dsimp [v]
    linarith
  apply survival_tendsto_zero_of_lyapunov _ (islandThreeTree_metzler k hc.le hq.le) v hv
    (a := 1) zero_lt_one _ i
  intro j
  have hf := congrFun (islandThree_potential_drifts k hc hq).1 j
  have hb := congrFun (islandThree_potential_drifts k hc hq).2 j
  have hr := islandThreeTree_rows_nonpos k (q := q) hc.le j
  have he : (islandThreeTreeGenerator k c q *ᵥ v) j =
      (∑ z, islandThreeTreeGenerator k c q j z) +
      (islandThreeTreeGenerator k c q *ᵥ islandThreeFirstPotential k c q) j +
      (islandThreeTreeGenerator k c q *ᵥ islandThreeDoublePotential k c q) j := by
    simp only [v,Matrix.mulVec,dotProduct,mul_add,mul_one,Finset.sum_add_distrib]
  rw [he,hf,hb]
  fin_cases j <;> simp_all [islandThreeFirstReward,islandThreeDoubleReward]

theorem islandThree_single_potential_drift (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    islandThreeTreeGenerator k c q *ᵥ
      (3 • islandThreeFirstPotential k c q + islandThreeDoublePotential k c q) =
      -islandThreeSingleReward := by
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,(islandThree_potential_drifts k hc hq).1,
    (islandThree_potential_drifts k hc hq).2]
  ext i
  fin_cases i <;> norm_num [islandThreeFirstReward,islandThreeDoubleReward,islandThreeSingleReward]

noncomputable def islandThreeExpectedBranch (k : ℕ) (c q : ℝ) (reward : Fin 5 → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), flowOutput (islandThreeTreeGenerator k c q) 0 reward 0 t

theorem islandThree_expected_spectrum (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    islandThreeExpectedBranch k c q islandThreeSingleReward =
      3*islandThreeFirstMean k c q + islandThreeDoubleMean k c q ∧
    islandThreeExpectedBranch k c q islandThreeDoubleReward = islandThreeDoubleMean k c q := by
  constructor
  · rw [islandThreeExpectedBranch,reward_integral_eq_potential _
      (islandThreeTree_metzler k hc.le hq.le) 0 _ _ (islandThree_single_potential_drift k hc hq)
      (by intro i; fin_cases i <;> norm_num [islandThreeSingleReward])
      (islandThree_survival_tendsto_zero k hc hq 0)]
    simp [islandThreeFirstPotential,islandThreeDoublePotential]
  · rw [islandThreeExpectedBranch,reward_integral_eq_potential _
      (islandThreeTree_metzler k hc.le hq.le) 0 _ _ (islandThree_potential_drifts k hc hq).2
      (by intro i; fin_cases i <;> norm_num [islandThreeDoubleReward])
      (islandThree_survival_tendsto_zero k hc hq 0)]
    simp [islandThreeDoublePotential]

theorem island_three_spectrum_has_exact_positive_size_match (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    ∃ u v τ : ℝ, 0 < u ∧ 0 < v ∧ 0 < τ ∧
      (∀ t, 0 < twoEpochSize u v τ t) ∧
      panThreeSpectrum (twoEpochSize u v τ) panThreeSingletonReward =
        islandThreeExpectedBranch k c q islandThreeSingleReward ∧
      panThreeSpectrum (twoEpochSize u v τ) panThreeDoubletonReward =
        islandThreeExpectedBranch k c q islandThreeDoubleReward := by
  apply every_three_spectrum_has_positive_twoEpoch_match
  · rw [(islandThree_expected_spectrum k hc hq).2]
    exact (islandThree_means_positive k hc hq).2
  · rw [(islandThree_expected_spectrum k hc hq).1,(islandThree_expected_spectrum k hc hq).2]
    linarith [(islandThree_means_positive k hc hq).1]

end Rhone.Statistics.Identifiability
