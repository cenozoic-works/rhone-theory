/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Tracked
public import Rhone.Coalescent.FiniteIntervalMaterialSamplerMeas

/-! # The capped-counter sampler update is Borel -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

theorem advancePhase_measurable :
    Measurable (fun p : Phase × Event => advancePhase p.1 p.2) := by
  classical
  have he : (fun p : Phase × Event => advancePhase p.1 p.2) =
      (fun p => if p.2 ∈ splitSet then
        (if p.1 = .zero then Phase.one else .two) else p.1) := by
    funext p
    cases h : p.1 <;> cases p.2 with
    | inl e => simp [advancePhase, splitSet]
    | inr e => cases e <;> simp [advancePhase, splitSet]
  rw [he]
  have hi : Measurable (fun p : Phase × Event =>
      if p.1 = .zero then Phase.one else .two) :=
    measurable_const.piecewise
      (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
  exact hi.piecewise (splitSet_measurable.preimage measurable_snd) measurable_fst

theorem trackedSampleStep_measurable (mode : Mode) (R : ℝ) :
    Measurable (fun p : TrackedState × Noise => trackedSampleStep mode R p.1 p.2) := by
  have hs : Measurable (fun p : TrackedState × Noise => sampleStep mode R p.1.1 p.2) :=
    (sampleStep_measurable mode R).comp (measurable_fst.fst.prodMk measurable_snd)
  have hp : Measurable (fun p : TrackedState × Noise =>
      advancePhase p.1.2.1 (sampleStep mode R p.1.1 p.2).2.2) :=
    advancePhase_measurable.comp (measurable_fst.snd.fst.prodMk hs.snd.snd)
  exact hs.fst.prodMk (hp.prodMk hs.snd)

end Rhone.Coalescent.SmcSupport
