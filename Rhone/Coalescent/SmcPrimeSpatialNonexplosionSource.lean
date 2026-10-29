/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialSource
public import Rhone.Analysis.WeightedAverage

/-!
# Nonexplosion of the full SMC′ spatial source recursion

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Filter

theorem sourceSpatialRun_gap_of_never_stop {N : ℕ} (R : ℝ) (z : SpatialState N)
    (u : ℕ → ProposalNoise) (hnever : ∀ k, (sourceSpatialRun N R z u k).1 ≠ 1) (k : ℕ) :
    0 < R ∧ 0 < treeLength (sourceSpatialRun N R z u k).2 ∧
    (sourceSpatialRun N R z u k).1 < 1 ∧
    (sourceSpatialRun N R z u (k + 1)).1 = (sourceSpatialRun N R z u k).1 +
      -Real.log (u k 0) / (R / 2 * treeLength (sourceSpatialRun N R z u k).2) := by
  have hs := hnever (k+1)
  change (spatialStep N R (sourceSpatialRun N R z u k) (u k)).1 ≠ 1 at hs
  have hstop : ¬ (1 ≤ (sourceSpatialRun N R z u k).1 ∨ R ≤ 0 ∨
      treeLength (sourceSpatialRun N R z u k).2 ≤ 0) := by
    intro h
    simp [spatialStep, h] at hs
  have hin : (sourceSpatialRun N R z u k).1 +
      (proposal R (sourceSpatialRun N R z u k).2 (u k)).1 < 1 := by
    by_contra h
    simp [spatialStep, hstop, h] at hs
  push Not at hstop
  refine ⟨hstop.2.1, hstop.2.2, hstop.1, ?_⟩
  simp only [sourceSpatialRun, spatialStep, hstop.1.not_ge, hstop.2.1.not_ge,
    hstop.2.2.not_ge, false_or, ↓reduceIte, hin]
  congr 1
  unfold proposal
  split <;> rfl

theorem sourceSpatialRun_stops_of_length_bound {N : ℕ} (R : ℝ) (z : SpatialState N)
    (u : ℕ → ProposalNoise) (hu : ∀ k i, u k i ∈ Set.Ioo 0 1)
    (hmean : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, -Real.log (u k 0)) / n)
      atTop (nhds 1)) (C : ℝ) (hC : 0 < C)
    (hlen : ∀ k, treeLength (sourceSpatialRun N R z u k).2 ≤ C * (k + 1)) :
    ∃ k, (sourceSpatialRun N R z u k).1 = 1 := by
  by_contra hnever
  push Not at hnever
  have hg := sourceSpatialRun_gap_of_never_stop R z u hnever
  have hR := (hg 0).1
  have he (k : ℕ) : 0 ≤ -Real.log (u k 0) :=
    neg_nonneg.mpr (Real.log_nonpos (hu k 0).1.le (hu k 0).2.le)
  have hbound (k : ℕ) :
      -Real.log (u k 0) / (k + 1) ≤ R / 2 * C *
        ((sourceSpatialRun N R z u (k+1)).1 - (sourceSpatialRun N R z u k).1) := by
    rw [(hg k).2.2.2, add_sub_cancel_left]
    have hr : 0 < R / 2 := by positivity
    have hL := (hg k).2.1
    have hden : 0 < R / 2 * treeLength (sourceSpatialRun N R z u k).2 := mul_pos hr hL
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    calc
      _ ≤ (R / 2 * C * -Real.log (u k 0) * (k+1)) /
          (R / 2 * treeLength (sourceSpatialRun N R z u k).2) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith [mul_le_mul_of_nonneg_left (hlen k) (mul_nonneg hr.le (he k))]
      _ = _ := by ring
  have hsums (n : ℕ) :
      (∑ k ∈ Finset.range n, -Real.log (u k 0) / (k+1)) ≤
        R / 2 * C * ((sourceSpatialRun N R z u n).1 - z.1) := by
    induction n with
    | zero => simp [sourceSpatialRun]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hh := hbound n
      linarith
  have hb : BddAbove (Set.range (fun n =>
      ∑ k ∈ Finset.range n, -Real.log (u k 0) / (k+1))) := by
    refine ⟨R / 2 * C * (1-z.1), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hsums n).trans (mul_le_mul_of_nonneg_left (by linarith [(hg n).2.2.1])
      (by positivity))
  have hzero := Rhone.Analysis.average_zero_of_bounded_weighted_sums
    (fun k => -Real.log (u k 0)) he hb
  have := tendsto_nhds_unique hmean hzero
  norm_num at this

theorem sourceSpatialRun_nonexplosive {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) :
    ∀ᵐ u ∂sourceProposalStreamLaw, ∃ k, (sourceSpatialRun N R z u k).1 = 1 := by
  filter_upwards [sourceProposalStreamLaw_ae_marks, sourceBudget_strong_law 0,
    sourceBudget_strong_law 3] with u hu hm0 hm3
  obtain ⟨B, hB⟩ := hm3.bddAbove_range
  have hB0 : 0 ≤ B := by simpa using hB (Set.mem_range_self 0)
  let C := treeLength z.2 + 2 * B + 1
  have hC : 0 < C := by dsimp [C]; linarith [treeLength_nonneg z.2]
  apply sourceSpatialRun_stops_of_length_bound R z u hu hm0 C hC
  intro k
  have hg := (sourceSpatialRun_geometry R z hN hnorm hnonneg hchron u hu k).2.2.2
  by_cases hk : k = 0
  · subst k
    simp only [sourceSpatialRun, Nat.cast_zero, zero_add, mul_one]
    dsimp [C]
    linarith
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hmeanBound := hB (Set.mem_range_self k)
    have hsum : (∑ j ∈ Finset.range k, -Real.log (u j 3)) ≤ B * k :=
      (div_le_iff₀ hk0).mp hmeanBound
    dsimp [C]
    nlinarith [treeLength_nonneg z.2]

end Rhone.Coalescent.SmcPrime
