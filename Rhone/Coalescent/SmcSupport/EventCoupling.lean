/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Coupling

/-! # Projection of the capped-counter coupling to the event processes -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory ProbabilityTheory

def forgetPhase (z : TrackedState) : AugmentedState := (z.1, z.2.2)

theorem samplerKernel_event (mode : Mode) (R : ℝ) (z : TrackedState) :
    (samplerKernel mode R z).map forgetPhase = eventKernel mode R (forgetPhase z) := by
  have hf : Measurable forgetPhase := measurable_fst.prodMk measurable_snd.snd
  have hs : Measurable (trackedSampleStep mode R z) :=
    (trackedSampleStep_measurable mode R).comp (measurable_const.prodMk measurable_id)
  rw [samplerKernel_apply, eventKernel_apply, Measure.map_map hf hs]
  rfl

theorem samplerProcess_event (mode : Mode) (R : ℝ) (z : TrackedState) :
    ((samplerProcess mode R).pathLaw z).map (fun ω k => forgetPhase (ω k)) =
      (eventProcess mode R).pathLaw (forgetPhase z) :=
  process_map_pathLaw (samplerProcess mode R) (eventProcess mode R) forgetPhase
    (measurable_fst.prodMk measurable_snd.snd) (samplerKernel_event mode R) z

theorem event_path_tv_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) :
    Rhone.Probability.eventTV
      ((eventProcess false R).pathLaw (initialState n, (0, .inl ())))
      ((eventProcess true R).pathLaw (initialState n, (0, .inl ()))) ≤
      ENNReal.ofReal (doubleBound R (n - 1)) := by
  have h := Probability.data_processing
    ((samplerProcess false R).pathLaw (trackedInitial n))
    ((samplerProcess true R).pathLaw (trackedInitial n))
    (fun ω k => forgetPhase (ω k))
    (measurable_pi_iff.mpr (fun k =>
      (measurable_fst.prodMk measurable_snd.snd).comp (measurable_pi_apply k)))
  rw [samplerProcess_event, samplerProcess_event] at h
  exact h.trans (sampler_path_tv_le R hR n hn)

theorem event_path_tv_quadratic (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) :
    Rhone.Probability.eventTV
      ((eventProcess false R).pathLaw (initialState n, (0, .inl ())))
      ((eventProcess true R).pathLaw (initialState n, (0, .inl ()))) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (n - 1))) := by
  exact (event_path_tv_le R hR n hn).trans (ENNReal.ofReal_le_ofReal
    (doubleBound_le_min R hR (n - 1)))

end Rhone.Coalescent.SmcSupport
