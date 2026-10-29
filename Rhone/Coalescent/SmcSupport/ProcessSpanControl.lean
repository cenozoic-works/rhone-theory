/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.StateSpanControl
public import Rhone.Coalescent.SmcSupport.JointSampler

/-! # Uniform bounds on hull span and split rate along contact trajectories -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

theorem eventProcess_totalHullSpan_le (R : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂(eventProcess true R).pathLaw (initialState n, (0, .inl ())),
      ∀ k, totalHullSpan (ω k).1 ≤ (n : ℝ) := by
  let A : AugmentedState × AugmentedState → Prop := fun p =>
    Valid p.1.1 → Valid p.2.1 ∧ totalHullSpan p.2.1 ≤ totalHullSpan p.1.1
  have hv : MeasurableSet {p : AugmentedState × AugmentedState | Valid p.1.1} :=
    validState_measurable.preimage measurable_fst.fst
  have hv' : MeasurableSet {p : AugmentedState × AugmentedState | Valid p.2.1} :=
    validState_measurable.preimage measurable_snd.fst
  have hl : MeasurableSet {p : AugmentedState × AugmentedState |
      totalHullSpan p.2.1 ≤ totalHullSpan p.1.1} :=
    measurableSet_le (totalHullSpan_measurable.comp measurable_snd.fst)
      (totalHullSpan_measurable.comp measurable_fst.fst)
  have hA : MeasurableSet {p | A p} := by
    convert hv.compl.union (hv'.inter hl) using 1
    ext p
    simp only [A, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, imp_iff_not_or]
  have hs (z : AugmentedState) : ∀ᵐ y ∂(eventProcess true R).step z, A (z, y) := by
    change ∀ᵐ y ∂eventKernel true R z, A (z, y)
    rw [eventKernel_apply]
    apply (ae_map_iff
      (show Measurable (fun u => sampleStep true R z.1 u) from
        (sampleStep_measurable true R).comp (measurable_const.prodMk measurable_id)).aemeasurable
      (hA.preimage measurable_prodMk_left)).mpr
    filter_upwards [noiseLaw_interior] with u hu
    intro hz
    exact ⟨sampleStep_valid true R z.1 hz u
      (hu 1).1.le (hu 1).2.le (hu 2).1 (hu 2).2,
      sampleStep_totalHullSpan_le R z.1 hz u
        (hu 0).1.le (hu 0).2 (hu 2).1 (hu 2).2⟩
  have ht := process_transition_relation (eventProcess true R) A hA hs
    (initialState n, (0, .inl ()))
  have hi : ∀ᵐ ω ∂(eventProcess true R).pathLaw (initialState n, (0, .inl ())),
      ω 0 = (initialState n, (0, .inl ())) := by
    apply ae_of_ae_map (f := fun ω : ℕ → AugmentedState => ω 0)
      (p := fun z => z = (initialState n, (0, .inl ()))) (measurable_pi_apply 0).aemeasurable
    rw [(eventProcess true R).map_eval_zero]
    exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).mpr rfl
  filter_upwards [ht, hi] with ω ht hi
  have hgood : ∀ k, Valid (ω k).1 ∧ totalHullSpan (ω k).1 ≤ (n : ℝ) := by
    intro k
    induction k with
    | zero =>
      rw [hi]
      exact ⟨initialState_valid n, (totalHullSpan_initial n).le⟩
    | succ k ih => exact ⟨(ht k ih.1).1, (ht k ih.1).2.trans ih.2⟩
  exact fun k => (hgood k).2

theorem eventProcess_splitRate_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ∀ᵐ ω ∂(eventProcess true R).pathLaw (initialState n, (0, .inl ())),
      ∀ k, (splitRate R (ω k).1 : ℝ) ≤ R * (n : ℝ) / 2 := by
  filter_upwards [eventProcess_totalHullSpan_le R n] with ω hω k
  rw [splitRate_eq_recombinationRate R hR]
  change R / 2 * totalHullSpan (ω k).1 ≤ _
  have h := mul_le_mul_of_nonneg_left (hω k) (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith

end Rhone.Coalescent.SmcSupport
