/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanThreeRewards
public import Rhone.Statistics.Identifiability.TwoEpochIntegral

/-! # Exact three-sample expected-spectrum overlap -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def panThreeSpectrum (η : ℝ → ℝ) (reward : Fin 2 → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), η t * flowOutput panThreeGenerator 0 reward 0 t

theorem log_epoch_moment {u v z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    {j : ℕ} (hj : 0 < j) :
    (∫ t in Ioi (0 : ℝ), twoEpochSize u v (-Real.log z) t * Real.exp (-(j:ℝ)*t)) =
      epochMoment u v z j := by
  rw [twoEpoch_laplace (by linarith [Real.log_neg hz hz1]) (by exact_mod_cast hj)]
  have he : Real.exp (-(j:ℝ)*(-Real.log z)) = z^j := by
    rw [neg_mul_neg,Real.exp_nat_mul,Real.exp_log hz]
  rw [he]
  rfl

theorem twoEpoch_three_spectrum {u v z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    panThreeSpectrum (twoEpochSize u v (-Real.log z)) panThreeSingletonReward =
      (3/2 : ℝ)*(epochMoment u v z 1 + epochMoment u v z 3) ∧
    panThreeSpectrum (twoEpochSize u v (-Real.log z)) panThreeDoubletonReward =
      (3/2 : ℝ)*(epochMoment u v z 1 - epochMoment u v z 3) := by
  have h1 := twoEpoch_weight_integrable (u := u) (v := v) (τ := -Real.log z) (α := 1) (by norm_num)
  have h3 := twoEpoch_weight_integrable (u := u) (v := v) (τ := -Real.log z) (α := 3) (by norm_num)
  have hm1 := log_epoch_moment (u := u) (v := v) hz hz1 (j := 1) (by norm_num)
  have hm3 := log_epoch_moment (u := u) (v := v) hz hz1 (j := 3) (by norm_num)
  norm_num only [Nat.cast_one,Nat.cast_ofNat,neg_mul,one_mul] at h1 h3 hm1 hm3
  constructor
  · unfold panThreeSpectrum
    calc
      _ = ∫ t in Ioi (0 : ℝ), (3/2 : ℝ)*
          (twoEpochSize u v (-Real.log z) t*Real.exp (-t) +
           twoEpochSize u v (-Real.log z) t*Real.exp (-3*t)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [(panThree_reward_formulas (le_of_lt ht)).1]
        ring
      _ = _ := by
        simp only [neg_mul]
        rw [integral_const_mul,integral_add h1 h3,hm1,hm3]
  · unfold panThreeSpectrum
    calc
      _ = ∫ t in Ioi (0 : ℝ), (3/2 : ℝ)*
          (twoEpochSize u v (-Real.log z) t*Real.exp (-t) -
           twoEpochSize u v (-Real.log z) t*Real.exp (-3*t)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [(panThree_reward_formulas (le_of_lt ht)).2]
        ring
      _ = _ := by
        simp only [neg_mul]
        rw [integral_const_mul,integral_sub h1 h3,hm1,hm3]

theorem every_three_spectrum_has_positive_twoEpoch_match {b₁ b₂ : ℝ}
    (h₂ : 0 < b₂) (h₁₂ : b₂ < b₁) :
    ∃ u v τ : ℝ, 0 < u ∧ 0 < v ∧ 0 < τ ∧
      (∀ t, 0 < twoEpochSize u v τ t) ∧
      panThreeSpectrum (twoEpochSize u v τ) panThreeSingletonReward = b₁ ∧
      panThreeSpectrum (twoEpochSize u v τ) panThreeDoubletonReward = b₂ := by
  obtain ⟨u,v,z,hu,hv,hz,hz1,hm1,hm3⟩ :=
    positive_twoEpoch_realization (d := (b₁+b₂)/3) (a := (b₁-b₂)/3)
      (by linarith) (by linarith)
  refine ⟨u,v,-Real.log z,hu,hv,by linarith [Real.log_neg hz hz1],
    twoEpochSize_pos hu hv,?_,?_⟩
  · rw [(twoEpoch_three_spectrum hz hz1).1,hm1,hm3]
    ring
  · rw [(twoEpoch_three_spectrum hz hz1).2,hm1,hm3]
    ring

end Rhone.Statistics.Identifiability
