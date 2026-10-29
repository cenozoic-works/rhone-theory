/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SamplerKernel
public import Rhone.Coalescent.SmcSupport.BranchValues
public import Rhone.Coalescent.SmcSupport.MarkedBarrier
public import Rhone.Coalescent.FiniteIntervalMaterialNoiseLaw

/-! # Integrating the sampled barrier from exact selector masses -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory

theorem integral_selected_reward (mode : Mode) (R : ℝ) (s : State)
    (ht : totalRate mode R s ≠ 0) (reward : ActionIndex s → ℝ) :
    (∫ u, ∑ a : ActionIndex s,
      {u | selectedAction mode R s u = some a}.indicator (fun _ => reward a) u
      ∂noiseLaw) =
      ∑ a : ActionIndex s,
        ((candidateRate mode R s a : ℝ) / (totalRate mode R s : ℝ)) * reward a := by
  classical
  let : MeasurableSpace (ActionIndex s) := ⊤
  let : MeasurableSpace (Option (ActionIndex s)) := ⊤
  have hm : Measurable (selectedAction mode R s) :=
    chooseByRate_measurable (fun a _ => (candidateRate mode R s a : ℝ))
      (fun _ => measurable_const) Finset.univ.toList
      (fun u : Noise => u 0 * (totalRate mode R s : ℝ))
      ((measurable_pi_apply 0).mul_const _)
  have hs (a : ActionIndex s) :
      MeasurableSet {u | selectedAction mode R s u = some a} :=
    hm (show MeasurableSet ({some a} : Set (Option (ActionIndex s))) from by trivial)
  rw [integral_finsetSum _ (fun a _ => (integrable_const (reward a)).indicator (hs a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator_const _ (hs a), measureReal_def,
    noiseLaw_selectedAction_mass mode R s (lt_of_le_of_ne (zero_le) (Ne.symm ht))]
  rw [ENNReal.toReal_ofReal (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))]
  rfl

theorem integral_selected_mixture (mode : Mode) (R : ℝ) (s : State)
    (hm : 1 < s.2.2.1) (ht : totalRate mode R s ≠ 0)
    (pairValue splitValue : ℝ) :
    (∫ u, ∑ a : ActionIndex s,
      {u | selectedAction mode R s u = some a}.indicator
        (fun _ => match a with | .inl _ => pairValue | .inr _ => splitValue) u
      ∂noiseLaw) =
    ∫ e, markMixtureReward pairValue splitValue e ∂markedLaw mode R s := by
  rw [integral_selected_reward mode R s ht, integral_markMixtureReward,
    markedLaw_coal_mass mode R s hm ht, markedLaw_split_mass mode R s hm ht]
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal, Fintype.sum_sum_type]
  simp only [← Finset.sum_mul, ← Finset.sum_div]
  simp only [coalRate, splitRate, NNReal.coe_sum]
  rfl

theorem integral_barrier_of_branch_values (mode : Mode) (R : ℝ) (z : TrackedState)
    (hm : 1 < z.1.2.2.1) (ht : 0 < totalRate mode R z.1)
    (pairValue splitValue : ℝ)
    (hp : ∀ u ij, selectedAction mode R z.1 u = some (.inl ij) →
      0 < candidateRate mode R z.1 (.inl ij) →
      barrier R (trackedSampleStep mode R z u) = pairValue)
    (hs : ∀ u i, selectedAction mode R z.1 u = some (.inr i) →
      barrier R (trackedSampleStep mode R z u) = splitValue) :
    (∫ y, barrier R y ∂samplerKernel mode R z) =
    ∫ e, markMixtureReward pairValue splitValue e ∂markedLaw mode R z.1 := by
  classical
  have hmap : Measurable (trackedSampleStep mode R z) :=
    (trackedSampleStep_measurable mode R).comp (measurable_const.prodMk measurable_id)
  rw [samplerKernel_apply, integral_map hmap.aemeasurable
    (barrier_measurable R).aestronglyMeasurable]
  rw [← integral_selected_mixture mode R z.1 hm (ne_of_gt ht)]
  apply integral_congr_ae
  filter_upwards [noiseLaw_interior] with u hu
  obtain ⟨a, ha, hpos⟩ := selectedAction_exists_positive mode R z.1 u
    (hu 0).1.le (hu 0).2 ht
  cases a with
  | inl ij => simpa [Set.indicator, ha] using hp u ij ha hpos
  | inr i => simpa [Set.indicator, ha] using hs u i ha

theorem barrier_step_le (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (z : TrackedState) (hz : Good z) :
    (∫ z', barrier R z' ∂samplerKernel mode R z) ≤ barrier R z := by
  classical
  have hmap : Measurable (trackedSampleStep mode R z) :=
    (trackedSampleStep_measurable mode R).comp (measurable_const.prodMk measurable_id)
  by_cases hm : z.1.2.2.1 ≤ 1
  · rw [samplerKernel_apply, integral_map hmap.aemeasurable
      (barrier_measurable R).aestronglyMeasurable]
    have he : ∀ u, barrier R (trackedSampleStep mode R z u) = barrier R z := by
      intro u
      cases hp : z.2.1 <;>
        simp [trackedSampleStep, sampleStep, hm, hp, advancePhase, barrier]
    simp_rw [he]
    simp
  · have hm2 : 2 ≤ z.1.2.2.1 := by omega
    cases hp : z.2.1 with
    | two =>
      rw [samplerKernel_apply, integral_map hmap.aemeasurable
        (barrier_measurable R).aestronglyMeasurable]
      have he : ∀ u, barrier R (trackedSampleStep mode R z u) = 1 := by
        intro u
        simp [barrier, trackedSampleStep_two mode R z hp u]
      simp_rw [he]
      simp [barrier, hp]
    | zero =>
      have hg : Valid z.1 ∧ AllMaterials FullAtoms z.1 ∧ 1 ≤ z.1.2.2.1 := by
        simpa [Good, hp] using hz
      have ht := contact_totalRate_positive mode R z.1 hm2 (full_contacts z.1 hg.2.1)
      rw [integral_barrier_of_branch_values mode R z (by omega) ht
        (doubleBound R (z.1.2.2.1 - 2)) (raceBound (hazard R) z.1.2.2.1)
        (fun u ij ha hpos => tracked_pair_zero_value mode R z hp hm2 ht u ij ha hpos)
        (fun u i ha => tracked_split_zero_value mode R z hp hm2 ht u i ha)]
      let m := z.1.2.2.1 - 2
      have hc : z.1.2.2.1 = (m + 1) + 1 := by dsimp [m]; omega
      let s : CountState (m + 1) := ⟨z.1, hg.1, hc⟩
      have he := marked_phase_zero_barrier mode R hR m s hg.2.1
      have hn : z.1.2.2.1 - 1 = m + 1 := by omega
      change (∫ e, markMixtureReward (doubleBound R m)
        (raceBound (hazard R) z.1.2.2.1) e ∂markedLaw mode R z.1) ≤ _
      rw [hc]
      change (∫ e, markMixtureReward (doubleBound R m)
        (raceBound (hazard R) (m + 2)) e ∂markedLaw mode R z.1) ≤ _
      rw [he]
      simp [barrier, hp, hn]
    | one =>
      have hg : Valid z.1 ∧
          (∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) ∧ 1 ≤ z.1.2.2.1 := by
        simpa [Good, hp] using hz
      have ht := contact_totalRate_positive mode R z.1 hm2 hg.2.1
      rw [integral_barrier_of_branch_values mode R z (by omega) ht
        (raceBound (hazard R) (z.1.2.2.1 - 2)) 1
        (fun u ij ha hpos => tracked_pair_one_value mode R z hp hm2 ht u ij ha hpos)
        (fun u i ha => tracked_split_one_value mode R z hp hm2 ht u i ha)]
      let m := z.1.2.2.1 - 2
      have hc : z.1.2.2.1 = (m + 1) + 1 := by dsimp [m]; omega
      let s : CountState (m + 1) := ⟨z.1, hg.1, hc⟩
      have he := marked_phase_one_barrier mode R hR m s hg.2.1
      have hn : z.1.2.2.1 - 1 = m + 1 := by omega
      simpa only [s, m, barrier, hp, hn] using he

end Rhone.Coalescent.SmcSupport
