/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.EventCoupling
public import Rhone.Coalescent.FiniteIntervalGenealogy

/-! # The event of two splits: measurability and probability bound -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory ProbabilityTheory

def eventTwoSplits : Set Rhone.Coalescent.IntervalProcess.EventPath :=
  {ω | ∃ i j : ℕ, i < j ∧ (ω (i + 1)).2.2 ∈ splitSet ∧
    (ω (j + 1)).2.2 ∈ splitSet}

theorem eventTwoSplits_measurable : MeasurableSet eventTwoSplits := by
  apply measurableSet_exists
  intro i
  apply measurableSet_exists
  intro j
  exact (MeasurableSet.const _).inter
    ((splitSet_measurable.preimage (measurable_pi_apply (i + 1)).snd.snd).inter
      (splitSet_measurable.preimage (measurable_pi_apply (j + 1)).snd.snd))

theorem samplerProcess_phase_update (mode : Mode) (R : ℝ) (z : TrackedState) :
    ∀ᵐ ω ∂(samplerProcess mode R).pathLaw z, ∀ k,
      (ω (k + 1)).2.1 = advancePhase (ω k).2.1 (ω (k + 1)).2.2.2 := by
  let A : TrackedState × TrackedState → Prop := fun p =>
    p.2.2.1 = advancePhase p.1.2.1 p.2.2.2.2
  have hA : MeasurableSet {p | A p} := measurableSet_eq_fun measurable_snd.snd.fst
    (advancePhase_measurable.comp (measurable_fst.snd.fst.prodMk measurable_snd.snd.snd.snd))
  apply process_transition_relation (samplerProcess mode R) A hA _ z
  intro x
  change ∀ᵐ y ∂samplerKernel mode R x, A (x, y)
  rw [samplerKernel_apply]
  apply (ae_map_iff
    ((trackedSampleStep_measurable mode R).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    (hA.preimage (measurable_const.prodMk measurable_id))).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem advancePhase_nonzero (p : Phase) (e : Event) (hp : p ≠ .zero) :
    advancePhase p e ≠ .zero := by
  cases p <;> cases e with
  | inl e => simp_all [advancePhase]
  | inr e => cases e <;> simp_all [advancePhase]

theorem tracked_two_split_marks (ω : ℕ → TrackedState)
    (hu : ∀ k, (ω (k + 1)).2.1 = advancePhase (ω k).2.1 (ω (k + 1)).2.2.2)
    (hb : (fun k => forgetPhase (ω k)) ∈ eventTwoSplits) :
    ∃ k, (ω k).2.1 = .two := by
  obtain ⟨i, j, hij, hi, hj⟩ := hb
  have hfirst : (ω (i + 1)).2.1 ≠ .zero := by
    rw [hu i]
    change (ω (i + 1)).2.2.2 ∈ splitSet at hi
    cases he : (ω (i + 1)).2.2.2 with
    | inl e => simp [he, splitSet] at hi
    | inr e => cases e with
      | inl e => simp [he, splitSet] at hi
      | inr e => cases (ω i).2.1 <;> simp [advancePhase]
  have hpersist : ∀ k, i + 1 ≤ k → (ω k).2.1 ≠ .zero := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hfirst
    | succ k _ ih => rw [hu k]; exact advancePhase_nonzero _ _ ih
  have hp := hpersist j (by omega)
  refine ⟨j + 1, ?_⟩
  rw [hu j]
  change (ω (j + 1)).2.2.2 ∈ splitSet at hj
  cases he : (ω (j + 1)).2.2.2 with
  | inl e => simp [he, splitSet] at hj
  | inr e => cases e with
    | inl e => simp [he, splitSet] at hj
    | inr e => cases hp' : (ω j).2.1 <;> simp_all [advancePhase]

theorem event_two_splits_le (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (N : ℕ) (hN : 0 < N) :
    ((eventProcess mode R).pathLaw (initialState N, (0, .inl ()))) eventTwoSplits ≤
      ENNReal.ofReal (doubleBound R (N - 1)) := by
  let μ := (samplerProcess mode R).pathLaw (trackedInitial N)
  have hm : Measurable (fun ω : ℕ → TrackedState => fun k => forgetPhase (ω k)) :=
    measurable_pi_iff.mpr (fun k =>
      (measurable_fst.prodMk measurable_snd.snd).comp (measurable_pi_apply k))
  have hsub : (fun ω k => forgetPhase (ω k)) ⁻¹' eventTwoSplits ≤ᵐ[μ]
      {ω | ∃ k, (ω k).2.1 = .two} := by
    filter_upwards [samplerProcess_phase_update mode R (trackedInitial N)] with ω hu
    exact tracked_two_split_marks ω hu
  have hbound : μ {ω | ∃ k, (ω k).2.1 = .two} ≤
      ENNReal.ofReal (doubleBound R (N - 1)) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
      (doubleBound_nonneg R hR (N - 1))).mpr (ever_second_split_le mode R hR N hN)
  have hmap := Measure.map_apply hm eventTwoSplits_measurable (μ := μ)
  rw [samplerProcess_event] at hmap
  exact hmap.trans_le ((measure_mono_ae hsub).trans hbound)

end Rhone.Coalescent.SmcSupport
