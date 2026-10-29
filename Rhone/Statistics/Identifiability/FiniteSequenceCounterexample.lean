/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.NonpanGrid
public import Rhone.Statistics.ThreeTipSites.FiniteGrid
public import Rhone.Statistics.Identifiability.FinitePanelConcentration

/-! # Non-pan laws with finite-site observations matching those of the unit pan -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Rhone.Statistics.Identifiability.FiniteSequenceCounterexample
open FinitePhase ThreeSampleMembership

lemma unit_pan_duration_laplace (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ p, Real.exp (-s * p.1 - t * p.2) ∂PanThreeSample.durationLaw (fun _ => 1)) =
      (3 / (3 + s)) * (1 / (1 + t)) := by
  rw [← FoldedCounts.comparator_pan_duration, FoldedCounts.comparator,
    FoldedCounts.scalar_duration_law]
  let := FoldedCounts.exponential_probability (by norm_num : (0 : ℝ) < 3)
  let := FoldedCounts.exponential_probability (by norm_num : (0 : ℝ) < 1)
  have he : (fun p : ℝ × ℝ => Real.exp (-s * p.1 - t * p.2)) =
      fun p => Real.exp (-s * p.1) * Real.exp (-t * p.2) := by
    funext p
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_prod_mul (fun x : ℝ => Real.exp (-s * x))
    (fun x : ℝ => Real.exp (-t * x)),
    ErlangPhase.exponential_laplace 3 s (by norm_num) hs,
    ErlangPhase.exponential_laplace 1 t (by norm_num) ht]

theorem exists_nonpan_matching_finite_sequence (L : ℕ) (k : ℝ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : Model n 1, IsProbabilityMeasure M.law ∧
      ¬PanRepresentable M.law ∧
      ∀ (K : ℕ) (π : ThreeTipSites.Roots K L),
        ThreeTipSites.law π k M.durationLaw =
          ThreeTipSites.law π k (PanThreeSample.durationLaw (fun _ => 1)) := by
  let s : Fin (3 * L + 1) → ℝ := fun i => (k / 2) * (i : ℕ)
  have hs : ∀ i, 0 ≤ s i := fun i => mul_nonneg (by positivity) (Nat.cast_nonneg _)
  obtain ⟨n, hn, M, hprob, hnon, hgrid⟩ :=
    ErlangPhase.exists_nonpan_model_duration_grid s hs 1 (by norm_num)
  let : IsProbabilityMeasure M.law := hprob
  let : IsProbabilityMeasure M.durationLaw :=
    by change IsProbabilityMeasure (Measure.map _ _); infer_instance
  let : IsProbabilityMeasure FoldedCounts.comparator.law :=
    FoldedCounts.comparator_probability
  let : IsProbabilityMeasure (PanThreeSample.durationLaw (fun _ => 1)) := by
    rw [← FoldedCounts.comparator_pan_duration]
    change IsProbabilityMeasure (Measure.map _ _)
    infer_instance
  refine ⟨n, hn, M, hprob, hnon, ?_⟩
  intro K π
  apply ThreeTipSites.law_eq_of_laplace_grid π hk.le M.durationLaw_nonnegative
    (PanThreeSample.durationLaw_nonnegative (fun _ => 1))
  intro i hi j _hj
  let q : Fin (3 * L + 1) := ⟨i, by omega⟩
  have ht : 0 ≤ (k / 2) * (j : ℝ) := mul_nonneg (by positivity) (Nat.cast_nonneg _)
  have he : ThreeTipSites.mode (k / 2) i j =
      fun p : ℝ × ℝ => Real.exp (-s q * p.1 - ((k / 2) * (j : ℝ)) * p.2) := by
    funext p
    unfold ThreeTipSites.mode s q
    congr 1
    ring
  rw [he, hgrid q _ ht, unit_pan_duration_laplace _ _ (hs q) ht]
  norm_num

theorem exists_nonpan_matching_iid_finite_sequence (L : ℕ) (k : ℝ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : Model n 1, IsProbabilityMeasure M.law ∧
      ¬PanRepresentable M.law ∧
      ∀ (K : ℕ) (π : ThreeTipSites.Roots K L) (N : ℕ),
        FinitePanelSampling.iidLaw (ThreeTipSites.law π k M.durationLaw) N =
          FinitePanelSampling.iidLaw
            (ThreeTipSites.law π k (PanThreeSample.durationLaw (fun _ => 1))) N := by
  obtain ⟨n, hn, M, hp, hnon, heq⟩ := exists_nonpan_matching_finite_sequence L k hk
  exact ⟨n, hn, M, hp, hnon, fun K π N => congrArg
    (fun μ => FinitePanelSampling.iidLaw μ N) (heq K π)⟩

end Rhone.Statistics.Identifiability.FiniteSequenceCounterexample
