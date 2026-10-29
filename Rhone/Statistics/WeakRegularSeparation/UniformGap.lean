/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.CommonBlock
public import Rhone.Statistics.WeakRegularSeparation.Pan

/-! # Alphabet-uniform finite-block separation from every proper pan comparator -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites
open FiniteBlockModel Algebra.Identifiability MarkovChain.Identifiability Identifiability

theorem uniform_gap_of_outside {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) [IsProbabilityMeasure μ] (hμ : NonnegativeJoint μ)
    (hout : encodedProbability k μ ∉ range compactPan) :
    ∃ L : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (K : ℕ) (hK : 2 ≤ K)
      (r : ℝ → ℝ) (_hr : LocallyIntegrable r volume) (_hn : ∀ t, 0 ≤ r t)
      (_ht : Tendsto (integratedClock r) atTop atTop) (l : ℝ), 0 ≤ l →
      ε ≤ blockDistance (K := K) (L := L) k l μ (uniformLift (PanThreeSample.durationLaw r))
        (show 0 < K by omega) := by
  classical
  obtain ⟨S, δ, hδ, hgap⟩ := finite_moment_gap_of_outside (encodedProbability k μ) hout
  obtain ⟨L, w, hw⟩ := common_block_words S
  refine ⟨L, δ / (S.card + 1), div_pos hδ (by positivity), ?_⟩
  intro K hK r hr hn ht l hl
  let := PanThreeSample.durationLaw_probability r hr hn ht
  let := panClockLaw_probability l r hr hn ht
  let ν := uniformLift (PanThreeSample.durationLaw r)
  have hν : NonnegativeJoint ν := uniform_lift_nonnegative _
    (PanThreeSample.durationLaw_nonnegative r)
  have hg := hgap (compactify (panClockLaw l r))
  rw [← pan_compact r hr hn ht hl] at hg
  have he (n : S) : |monoMoment n.val (encodedProbability k μ) -
      monoMoment n.val (encodedProbability l ν)| ≤
      blockDistance (K := K) (L := L) k l μ ν (show 0 < K by omega) := by
    have hh := padded_moment_distance hK hk hl μ ν hμ hν (w n)
    change |(∫ x : Cube 3, ∏ i, (x i).val ^ n.val i ∂μ.map (encode k)) -
      (∫ x : Cube 3, ∏ i, (x i).val ^ n.val i ∂ν.map (encode l))| ≤ _
    simpa only [hw n] using hh
  have hsum : (∑ n ∈ S, |monoMoment n (encodedProbability k μ) -
      monoMoment n (encodedProbability l ν)|) ≤
      S.card * blockDistance (K := K) (L := L) k l μ ν (show 0 < K by omega) := by
    calc
      _ ≤ ∑ _n ∈ S, blockDistance (K := K) (L := L) k l μ ν (show 0 < K by omega) :=
        Finset.sum_le_sum (fun n hnS => he ⟨n, hnS⟩)
      _ = _ := by simp
  have hd : 0 ≤ blockDistance (K := K) (L := L) k l μ ν (show 0 < K by omega) :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (div_le_iff₀ (show (0 : ℝ) < S.card + 1 by positivity)).mpr
  dsimp only [ν] at hsum hd
  nlinarith

end Rhone.Statistics.WeakRegularSeparation
