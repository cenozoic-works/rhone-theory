/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.DurationProduct
public import Rhone.Statistics.Identifiability.ScalarPostZeroOnset
public import Rhone.Statistics.Identifiability.FinitePhaseInitialDerivative
public import Rhone.Statistics.Identifiability.IndexedErlangInterpolation

/-! # Existence of non-pan Erlang-phase models matching a duration grid -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Matrix Topology
namespace Rhone.Statistics.ErlangPhase
open Algebra.Identifiability MarkovChain.Identifiability Identifiability FinitePhase
    ThreeSampleMembership
variable {J N : ℕ}

lemma model_nonpan (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N) (hNtwo : 2 ≤ N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hb : 0 < b) :
    ¬PanRepresentable (model r w b hN hr hw hsum hb).law := by
  have hJ : J ≠ 0 := by
    intro h
    subst J
    simp at hsum
  let : NeZero (J * N) := ⟨Nat.mul_ne_zero hJ (Nat.ne_of_gt hN)⟩
  let := model_probability r w b hN hr hw hsum hb
  apply (model r w b hN hr hw hsum hb).not_pan_of_scalar_post_zero_onset
  apply (model r w b hN hr hw hsum hb).initial_derivative_zero_of_exit
  exact initial_exit_zero r w hNtwo

theorem exists_nonpan_model_duration_grid {d : ℕ} (s : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i) (b : ℝ) (hb : 0 < b) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : Model n 1, IsProbabilityMeasure M.law ∧
      ¬PanRepresentable M.law ∧
      ∀ i (t : ℝ), 0 ≤ t →
        (∫ p, Real.exp (-s i * p.1 - t * p.2) ∂M.durationLaw) =
          (3 * b / (3 * b + s i)) * (b / (b + t)) := by
  obtain ⟨k, J, hJ, _hcard, w, r, hw, hr, hsum, heq⟩ :=
    (ErlangApproximation.eventually_indexed_erlang_match s hs
      (by linarith : 0 < 3 * b)).exists
  have hN : 0 < k + 2 := by omega
  let M := model r w b hN hr hw hsum hb
  refine ⟨J * (k + 2), Nat.mul_pos hJ hN, M,
    model_probability r w b hN hr hw hsum hb,
    model_nonpan r w b hN (by omega) hr hw hsum hb, ?_⟩
  intro i t ht
  rw [model_duration_laplace r w b hN hr hw hsum hb (s i) t (hs i) ht, heq i]

end Rhone.Statistics.ErlangPhase
