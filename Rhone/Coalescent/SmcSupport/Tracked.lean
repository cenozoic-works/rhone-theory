/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Barrier
public import Rhone.Coalescent.SmcSupport.Agreement

/-! # The tracked sampler step: state update with the split-count phase -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

noncomputable def trackedSampleStep (mode : Mode) (R : ℝ)
    (z : TrackedState) (u : Noise) : TrackedState :=
  let sr := sampleStep mode R z.1 u
  (sr.1, advancePhase z.2.1 sr.2.2, sr.2)

theorem trackedSampleStep_state (mode : Mode) (R : ℝ)
    (z : TrackedState) (u : Noise) :
    (trackedSampleStep mode R z u).1 = (sampleStep mode R z.1 u).1 := rfl

theorem trackedSampleStep_two (mode : Mode) (R : ℝ)
    (z : TrackedState) (hz : z.2.1 = .two) (u : Noise) :
    (trackedSampleStep mode R z u).2.1 = .two := by
  simp [trackedSampleStep, hz, advancePhase]

theorem trackedSampleStep_agreement (R : ℝ) (z : TrackedState) (u : Noise)
    (hz : ∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) :
    trackedSampleStep false R z u = trackedSampleStep true R z u := by
  unfold trackedSampleStep
  rw [sampleStep_agreement R z.1 u hz]

end Rhone.Coalescent.SmcSupport
