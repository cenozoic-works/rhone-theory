/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Tracked
public import Rhone.Coalescent.SmcSupport.Selector
public import Rhone.Coalescent.SmcSupport.Successors

/-! # Barrier values are determined by the selected sampler branch -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

theorem tracked_pair_zero_value (mode : Mode) (R : ℝ) (z : TrackedState)
    (hz : z.2.1 = .zero) (hm : 2 ≤ z.1.2.2.1)
    (ht : 0 < totalRate mode R z.1) (u : Noise)
    (ij : Fin z.1.2.2.1 × Fin z.1.2.2.1)
    (ha : selectedAction mode R z.1 u = some (.inl ij))
    (hp : 0 < candidateRate mode R z.1 (.inl ij)) :
    barrier R (trackedSampleStep mode R z u) = doubleBound R (z.1.2.2.1 - 2) := by
  classical
  have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate mode R z.1 = 0) := by
    intro h
    rcases h with h | h
    · omega
    · exact (ne_of_gt ht) h
  have hc := coalSuccessor_count z.1 ij.1 ij.2 (positive_pair_order mode R z.1 ij hp)
  have hn : (coalSuccessor z.1 ij.1 ij.2).2.2.1 - 1 = z.1.2.2.1 - 2 := by omega
  simp [trackedSampleStep, sampleStep, hstop, ha, hz, advancePhase, barrier, atTime, hn]

theorem tracked_pair_one_value (mode : Mode) (R : ℝ) (z : TrackedState)
    (hz : z.2.1 = .one) (hm : 2 ≤ z.1.2.2.1)
    (ht : 0 < totalRate mode R z.1) (u : Noise)
    (ij : Fin z.1.2.2.1 × Fin z.1.2.2.1)
    (ha : selectedAction mode R z.1 u = some (.inl ij))
    (hp : 0 < candidateRate mode R z.1 (.inl ij)) :
    barrier R (trackedSampleStep mode R z u) = raceBound (hazard R) (z.1.2.2.1 - 2) := by
  classical
  have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate mode R z.1 = 0) := by
    intro h
    rcases h with h | h
    · omega
    · exact (ne_of_gt ht) h
  have hc := coalSuccessor_count z.1 ij.1 ij.2 (positive_pair_order mode R z.1 ij hp)
  have hn : (coalSuccessor z.1 ij.1 ij.2).2.2.1 - 1 = z.1.2.2.1 - 2 := by omega
  simp [trackedSampleStep, sampleStep, hstop, ha, hz, advancePhase, barrier, atTime, hn]

theorem tracked_split_zero_value (mode : Mode) (R : ℝ) (z : TrackedState)
    (hz : z.2.1 = .zero) (hm : 2 ≤ z.1.2.2.1)
    (ht : 0 < totalRate mode R z.1) (u : Noise) (i : Fin z.1.2.2.1)
    (ha : selectedAction mode R z.1 u = some (.inr i)) :
    barrier R (trackedSampleStep mode R z u) = raceBound (hazard R) z.1.2.2.1 := by
  classical
  have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate mode R z.1 = 0) := by
    intro h
    rcases h with h | h
    · omega
    · exact (ne_of_gt ht) h
  have hn := fun x => splitSuccessor_count z.1 i x
  simp [trackedSampleStep, sampleStep, hstop, ha, hz, advancePhase, barrier, atTime, hn]

theorem tracked_split_one_value (mode : Mode) (R : ℝ) (z : TrackedState)
    (hz : z.2.1 = .one) (hm : 2 ≤ z.1.2.2.1)
    (ht : 0 < totalRate mode R z.1) (u : Noise) (i : Fin z.1.2.2.1)
    (ha : selectedAction mode R z.1 u = some (.inr i)) :
    barrier R (trackedSampleStep mode R z u) = 1 := by
  classical
  have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate mode R z.1 = 0) := by
    intro h
    rcases h with h | h
    · omega
    · exact (ne_of_gt ht) h
  simp [trackedSampleStep, sampleStep, hstop, ha, hz, advancePhase, barrier]

end Rhone.Coalescent.SmcSupport
