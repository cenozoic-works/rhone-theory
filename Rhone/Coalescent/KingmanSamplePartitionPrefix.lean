/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartition
public import Rhone.Coalescent.SmcPrimeKingmanPrefix
/-! # Prefix dependence of the sample partition -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory IntervalProcess

theorem samplePartition_eq_of_prefix (N : ℕ) (ω η : EventPath) (k : ℕ)
    (h : ∀ l, l ≤ k → ω l = η l) :
    samplePartition N ω k = samplePartition N η k := by
  classical
  apply Finpartition.ext
  have ha (i : Fin N) := ancestorLabel_eq_of_prefix N ω η leftBoundaryProbe i k h
  simp only [samplePartition_parts, kingmanSampleClades, ha]

theorem samplePartition_update_next (N : ℕ) (ω : EventPath) (k : ℕ)
    (y : AugmentedState) (l : ℕ) (hl : l ≤ k) :
    samplePartition N (Function.update ω (k + 1) y) l = samplePartition N ω l := by
  apply samplePartition_eq_of_prefix
  intro j hj
  exact Function.update_of_ne (show j ≠ k + 1 by omega) y ω

theorem samplePartition_update_measurable (N : ℕ) (ω : EventPath) (k : ℕ) :
    Measurable (fun y : AugmentedState =>
      samplePartition N (Function.update ω (k + 1) y) (k + 1)) := by
  apply (samplePartition_measurable N (k + 1)).comp
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j = k + 1
  · subst j
    simpa only [Function.update_self] using
      (measurable_id' : Measurable (fun y : AugmentedState => y))
  · simpa only [Function.update_of_ne hj] using
      (measurable_const (a := ω j) : Measurable (fun _ : AugmentedState => ω j))

theorem samplePartition_succ_idle (N : ℕ) (ω : EventPath) (k : ℕ)
    (hmark : (ω (k + 1)).2.2 = .inl ()) :
    samplePartition N ω (k + 1) = samplePartition N ω k := by
  classical
  apply Finpartition.ext
  simp only [samplePartition_parts, kingmanSampleClades, ancestorLabel, hmark, ancestorStep]
end Rhone.Coalescent.SmcPrime
