/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
public import Rhone.Statistics.Identifiability.VectorPrimitiveAC
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Volterra series solution: summability, continuity, and absolute continuity -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Nat

namespace Rhone.Statistics.Identifiability.VolterraSeriesSolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {A : ℝ → E →L[ℝ] E} {x : E}

theorem term_summable
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) (t : ℝ) :
    Summable (fun n => PeanoBaker.term A x n t) := by
  obtain ⟨u, hu, hbound⟩ := hb t t
  exact hu.of_norm_bounded (fun n => hbound n t (by simp))

theorem solution_continuous (hA : LocallyIntegrable A volume)
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) :
    Continuous (PeanoBaker.solution A x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨u, hu, hbound⟩ := hb (t-1) (t+1)
  have hc : ContinuousOn (PeanoBaker.solution A x) (uIcc (t-1) (t+1)) :=
    continuousOn_tsum (fun n => (LocallyIntegrablePeanoBaker.term_continuous hA x n).continuousOn)
      hu hbound
  apply hc.continuousAt
  rw [uIcc_of_le (by linarith : t-1 ≤ t+1)]
  exact Icc_mem_nhds (by linarith) (by linarith)

theorem solution_zero
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) :
    PeanoBaker.solution A x 0 = x := by
  rw [PeanoBaker.solution, (term_summable hb 0).tsum_eq_zero_add]
  simp

theorem hasSum_integral (hA : LocallyIntegrable A volume)
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) (t : ℝ) :
    HasSum (fun n => PeanoBaker.term A x (n+1) t)
      (∫ s in (0 : ℝ)..t, A s (PeanoBaker.solution A x s)) := by
  obtain ⟨u, hu, hbound⟩ := hb 0 t
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n s => ‖A s‖ * u n)
  · intro n
    exact (LocallyIntegrablePeanoBaker.term_integrable hA x n).aestronglyMeasurable.restrict
  · intro n
    filter_upwards with s hs
    exact ((A s).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbound n s (uIoc_subset_uIcc hs)) (norm_nonneg _))
  · filter_upwards with s _
    exact hu.mul_left ‖A s‖
  · simp_rw [tsum_mul_left]
    exact (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable
      (LocallyIntegrablePeanoBaker.norm_locallyIntegrable hA) 0 t).mul_const _
  · filter_upwards with s _
    exact (A s).hasSum (term_summable hb s).hasSum

theorem solution_integral_eq (hA : LocallyIntegrable A volume)
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) (t : ℝ) :
    PeanoBaker.solution A x t = x + ∫ s in (0 : ℝ)..t, A s (PeanoBaker.solution A x s) := by
  rw [PeanoBaker.solution, (term_summable hb t).tsum_eq_zero_add]
  rw [(hasSum_integral hA hb t).tsum_eq]
  rfl

theorem solution_ae_hasDerivAt (hA : LocallyIntegrable A volume)
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) :
    ∀ᵐ t, HasDerivAt (PeanoBaker.solution A x) (A t (PeanoBaker.solution A x t)) t := by
  have hi := LocallyIntegrablePeanoBaker.locallyIntegrable_apply hA (solution_continuous hA hb)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hi] with t ht
  have heq : PeanoBaker.solution A x =
      fun t => x + ∫ s in (0 : ℝ)..t, A s (PeanoBaker.solution A x s) :=
    funext (solution_integral_eq hA hb)
  rw [heq]
  convert (ht 0).const_add x using 1
  rw [← heq]

theorem solution_absolutelyContinuousOnInterval (hA : LocallyIntegrable A volume)
    (hb : ∀ a b : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (PeanoBaker.solution A x) a b := by
  have hi := LocallyIntegrablePeanoBaker.locallyIntegrable_apply hA (solution_continuous hA hb)
  have hrepr : PeanoBaker.solution A x =
      fun t => PeanoBaker.solution A x a + ∫ s in a..t, A s (PeanoBaker.solution A x s) := by
    funext t
    conv_lhs => rw [solution_integral_eq hA hb t]
    conv_rhs => rw [solution_integral_eq hA hb a]
    rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals
      (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hi 0 a)
      (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hi a t)]
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => PeanoBaker.solution A x a) a b :=
    (LipschitzWith.const (PeanoBaker.solution A x a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hp := VectorPrimitiveAC.intervalIntegral_absolutelyContinuousOnInterval_banach
    (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hi a b)
    (left_mem_uIcc : a ∈ uIcc a b)
  rw [hrepr]
  exact hc.add hp

end Rhone.Statistics.Identifiability.VolterraSeriesSolution
