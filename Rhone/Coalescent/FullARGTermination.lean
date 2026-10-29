/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FullARGTerminationFoster
public import Rhone.Coalescent.FullARGTerminationDrift
public import Rhone.Coalescent.FiniteIntervalGenealogyLawSupport

/-!
# Termination of the unrestricted backward process behind `fullARGGenealogyLaw`

Source: griffiths_marjoram1997, sec. 1; griffiths1991_two_locus_graph, Thm 1, p. 103, p. 107. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory ProbabilityTheory SmcSupport
open scoped ENNReal

theorem eventProcess_liveCount_reaches_one (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1 := by
  have h := MarkovChain.IntervalProcess.pathLaw_ae_exists_notMem_of_drift (eventProcess false R)
    (absorptionPotential_measurable R) activeStates_measurable
    (eventKernel_absorptionPotential_drift R hR) (initialState N, (0, .inl ()))
    (by rw [absorptionPotential_initial]; exact ENNReal.ofReal_ne_top)
  filter_upwards [h] with ω hω
  obtain ⟨K, hK⟩ := hω
  exact ⟨K, fun k hk => Nat.le_of_lt_succ (Nat.lt_of_not_ge (hK k hk))⟩

theorem eventProcess_active_events_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∑' k, (eventProcess false R).pathLaw (initialState N, (0, .inl ()))
      {ω | 2 ≤ (ω k).1.2.2.1} ≤ ENNReal.ofReal (absorptionBudget R N) := by
  have h := MarkovChain.IntervalProcess.pathLaw_tsum_measure_le_of_drift (eventProcess false R)
    (absorptionPotential_measurable R) activeStates_measurable
    (eventKernel_absorptionPotential_drift R hR) (initialState N, (0, .inl ()))
  rw [absorptionPotential_initial] at h
  exact h

theorem eventProcess_total_time_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ ω, ⨆ k, ENNReal.ofReal (ω k).1.1
      ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  have htime : Measurable (fun y : AugmentedState => ENNReal.ofReal y.1.1) :=
    ENNReal.measurable_ofReal.comp measurable_fst.fst
  have hV : Measurable (fun y : AugmentedState =>
      absorptionPotential R y + ENNReal.ofReal y.1.1) :=
    (absorptionPotential_measurable R).add htime
  have hdrift : ∀ s : AugmentedState,
      ∫⁻ y, (absorptionPotential R y + ENNReal.ofReal y.1.1) ∂(eventProcess false R).step s +
        (0 : AugmentedState → ℝ≥0∞) s ≤ absorptionPotential R s + ENNReal.ofReal s.1.1 := by
    intro s
    change ∫⁻ y, (absorptionPotential R y + ENNReal.ofReal y.1.1) ∂eventKernel false R s +
      0 ≤ _
    rw [add_zero, lintegral_add_left (absorptionPotential_measurable R)]
    calc
      ∫⁻ y, absorptionPotential R y ∂eventKernel false R s +
          ∫⁻ y, ENNReal.ofReal y.1.1 ∂eventKernel false R s ≤
          ∫⁻ y, absorptionPotential R y ∂eventKernel false R s +
            (ENNReal.ofReal s.1.1 + activeStates.indicator 1 s) :=
        add_le_add le_rfl (eventKernel_time_drift R s)
      _ = (∫⁻ y, absorptionPotential R y ∂eventKernel false R s +
            activeStates.indicator 1 s) + ENNReal.ofReal s.1.1 := by ring
      _ ≤ absorptionPotential R s + ENNReal.ofReal s.1.1 :=
        add_le_add (eventKernel_absorptionPotential_drift R hR s) le_rfl
  have hstart : absorptionPotential R (initialState N, (0, .inl ())) +
      ENNReal.ofReal (initialState N, ((0 : ℝ), (.inl () : Event))).1.1 =
      ENNReal.ofReal (absorptionBudget R N) := by
    rw [absorptionPotential_initial]
    change _ + ENNReal.ofReal 0 = _
    rw [ENNReal.ofReal_zero, add_zero]
  have hn : ∀ n, ∫⁻ ω, ENNReal.ofReal (ω n).1.1
      ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) ≤
      ENNReal.ofReal (absorptionBudget R N) := by
    intro n
    have h := MarkovChain.IntervalProcess.pathLaw_drift_le (eventProcess false R) hV measurable_zero
        hdrift
      (initialState N, (0, .inl ())) n
    rw [hstart] at h
    exact le_trans (le_trans (lintegral_mono fun ω => le_add_self) le_self_add) h
  have hmono : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      Monotone fun k => ENNReal.ofReal (ω k).1.1 := by
    filter_upwards [eventProcess_chronologicalAncestryPath N false R] with ω h
    exact fun a b hab => ENNReal.ofReal_le_ofReal (h.time_monotone hab)
  have hsup := lintegral_iSup'
    (μ := (eventProcess false R).pathLaw (initialState N, (0, .inl ())))
    (f := fun (k : ℕ) (ω : EventPath) => ENNReal.ofReal (ω k).1.1)
    (fun k => (htime.comp (measurable_pi_apply k)).aemeasurable) hmono
  rw [hsup]
  exact iSup_le hn

theorem genealogyObservation_le_time_of_one {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (K : ℕ) (hK : (ω K).1.2.2.1 ≤ 1)
    (q : GenomicProbe) (i j : Fin N) :
    genealogyObservation N ω q i j ≤ ENNReal.ofReal (ω K).1.1 := by
  have hc : CompletedCoverage (ω K).1 := fun _ a b _ _ =>
    Fin.ext (by have := a.isLt; have := b.isLt; omega)
  have he := h.completed_of_coverage K hc q i j
  change (⨅ k : ℕ, if ancestorLabel N ω q i k = ancestorLabel N ω q j k
    then ENNReal.ofReal (ω k).1.1 else ⊤) ≤ _
  exact iInf_le_of_le K (by rw [ite_eq_left he])

theorem fullARGGenealogyLaw_ae_finite (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ G ∂fullARGGenealogyLaw N R, ∀ q i j, G q i j < ⊤ := by
  have hfin : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      ∀ q i j, genealogyObservation N ω q i j < ⊤ := by
    filter_upwards [eventProcess_chronologicalAncestryPath N false R,
      eventProcess_liveCount_reaches_one N R hR] with ω h hω
    obtain ⟨K, hK⟩ := hω
    intro q i j
    exact lt_of_le_of_lt (genealogyObservation_le_time_of_one h K (hK K le_rfl) q i j)
      ENNReal.ofReal_lt_top
  unfold fullARGGenealogyLaw
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have hcoord : Measurable (fun G : Genealogy N => G q i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply q))
  refine (ae_map_iff (genealogyObservation_measurable N).aemeasurable
    (measurableSet_lt hcoord measurable_const)).mpr ?_
  filter_upwards [hfin] with ω h using h q i j

theorem fullARGGenealogyLaw_lintegral_iSup_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ G, ⨆ q, ⨆ i, ⨆ j, G q i j ∂fullARGGenealogyLaw N R ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  have hsup : Measurable (fun G : Genealogy N => ⨆ q, ⨆ i, ⨆ j, G q i j) :=
    Measurable.iSup fun q => Measurable.iSup fun i => Measurable.iSup fun j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply q))
  unfold fullARGGenealogyLaw
  rw [lintegral_map hsup (genealogyObservation_measurable N)]
  refine le_trans (lintegral_mono_ae ?_) (eventProcess_total_time_le N R hR)
  filter_upwards [eventProcess_chronologicalAncestryPath N false R,
    eventProcess_liveCount_reaches_one N R hR] with ω h hω
  obtain ⟨K, hK⟩ := hω
  exact iSup_le fun q => iSup_le fun i => iSup_le fun j =>
    (genealogyObservation_le_time_of_one h K (hK K le_rfl) q i j).trans
      (le_iSup (fun k => ENNReal.ofReal (ω k).1.1) K)

end Rhone.Coalescent.IntervalProcess
