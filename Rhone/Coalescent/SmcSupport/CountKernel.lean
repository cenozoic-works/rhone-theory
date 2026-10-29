/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.StateSpanControl
public import Rhone.Coalescent.SmcSupport.CountBudget
public import Rhone.Coalescent.SmcSupport.SampledBarrier
public import Rhone.Coalescent.FiniteIntervalGenealogyMeas

/-! # The sampler count mixture spends the finite absorption budget -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

theorem integral_event_count (mode : Mode) (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (ht : 0 < totalRate mode R z.1) (f : ℕ → ℝ) :
    (∫ y, f (y.1.2.2.1 - 1) ∂eventKernel mode R z) =
      (1 - (markedLaw mode R z.1 splitSet).toReal) * f (z.1.2.2.1 - 2) +
      (markedLaw mode R z.1 splitSet).toReal * f z.1.2.2.1 := by
  classical
  have hf : Measurable (fun y : AugmentedState => f (y.1.2.2.1 - 1)) :=
    (measurable_of_countable f).comp
      ((liveCount_measurable.comp measurable_fst).sub_const 1)
  have hmap : Measurable (fun u => sampleStep mode R z.1 u) :=
    (sampleStep_measurable mode R).comp (measurable_const.prodMk measurable_id)
  have he : (∫ y, f (y.1.2.2.1 - 1) ∂eventKernel mode R z) =
      ∫ e, markMixtureReward (f (z.1.2.2.1 - 2)) (f z.1.2.2.1) e
        ∂markedLaw mode R z.1 := by
    rw [eventKernel_apply, integral_map hmap.aemeasurable hf.aestronglyMeasurable,
      ← integral_selected_mixture mode R z.1 hm (ne_of_gt ht)]
    apply integral_congr_ae
    filter_upwards [noiseLaw_interior] with u hu
    obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive mode R z.1 u
      (hu 0).1.le (hu 0).2 ht
    cases a with
    | inl ij =>
      have hc := coalSuccessor_count z.1 ij.1 ij.2 (positive_pair_order mode R z.1 ij hp)
      have hex : (coalSuccessor z.1 ij.1 ij.2).2.2.1 - 1 = z.1.2.2.1 - 2 := by omega
      simp [sampleStep, Nat.not_le.mpr hm, ne_of_gt ht, ha, atTime, hex, Set.indicator]
    | inr i =>
      simp [sampleStep, Nat.not_le.mpr hm, ne_of_gt ht, ha, atTime,
        splitSuccessor_count, Set.indicator]
  rw [integral_markMixtureReward] at he
  have hc : (markedLaw mode R z.1 coalSet).toReal =
      1 - (markedLaw mode R z.1 splitSet).toReal := by
    linarith [marked_branch_mass_sum mode R z.1 hm (ne_of_gt ht)]
  simpa only [hc] using he

theorem marked_split_prob_le (R : ℝ) (hR : 0 ≤ R) (N : ℕ) (s : State)
    (hm : 1 < s.2.2.1) (hspan : totalHullSpan s ≤ (N : ℝ))
    (hcoal : ((s.2.2.1 - 1 : ℕ) : ℝ) ≤ (coalRate true s : ℝ)) :
    (markedLaw true R s splitSet).toReal ≤
      (R * (N : ℝ) / 2) / (R * (N : ℝ) / 2 + ((s.2.2.1 - 1 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < (s.2.2.1 - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hb : (splitRate R s : ℝ) ≤ R * (N : ℝ) / 2 := by
    rw [splitRate_eq_recombinationRate R hR]
    change R / 2 * totalHullSpan s ≤ _
    have h := mul_le_mul_of_nonneg_left hspan (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have ht : 0 < totalRate true R s := by
    rw [totalRate_eq]
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hn.trans_le hcoal) (by positivity)
  rw [markedLaw_split_mass true R s hm (ne_of_gt ht), ENNReal.toReal_div,
    ENNReal.coe_toReal, ENNReal.coe_toReal, totalRate_eq, NNReal.coe_add]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (hn.trans_le hcoal)
      (by positivity : 0 ≤ (splitRate R s : ℝ)))
    (add_pos_of_nonneg_of_pos (by positivity) hn)).mpr
  have h1 := mul_le_mul_of_nonneg_right hb hn.le
  have h2 := mul_le_mul_of_nonneg_left hcoal (by positivity : 0 ≤ R * (N : ℝ) / 2)
  nlinarith

theorem eventKernel_countBudget_le (R : ℝ) (hR : 0 ≤ R) (N M : ℕ)
    (z : AugmentedState) (hm : 1 < z.1.2.2.1)
    (hspan : totalHullSpan z.1 ≤ (N : ℝ))
    (hcoal : ((z.1.2.2.1 - 1 : ℕ) : ℝ) ≤ (coalRate true z.1 : ℝ))
    (hM : 2 * (R * (N : ℝ) / 2) ≤ (M : ℝ)) :
    (∫ y, countBudget (R * (N : ℝ) / 2) M (y.1.2.2.1 - 1)
      ∂eventKernel true R z) ≤
      countBudget (R * (N : ℝ) / 2) M (z.1.2.2.1 - 1) - 1 := by
  have hn : 0 < z.1.2.2.1 - 1 := by omega
  have ht : 0 < totalRate true R z.1 := by
    rw [totalRate_eq]
    exact add_pos_of_pos_of_nonneg
      (by exact_mod_cast (Nat.cast_pos.mpr hn : (0 : ℝ) < (z.1.2.2.1 - 1 : ℕ)).trans_le hcoal)
      (by positivity)
  rw [integral_event_count true R z hm ht]
  have he := countBudget_step_le (R * (N : ℝ) / 2) (by positivity) M
    (z.1.2.2.1 - 1) hM hn (markedLaw true R z.1 splitSet).toReal
    ENNReal.toReal_nonneg (marked_split_prob_le R hR N z.1 hm hspan hcoal)
  have he1 : z.1.2.2.1 - 1 + 1 = z.1.2.2.1 := by omega
  have he2 : z.1.2.2.1 - 1 - 1 = z.1.2.2.1 - 2 := by omega
  simpa only [he1, he2, add_comm] using he

end Rhone.Coalescent.SmcSupport
