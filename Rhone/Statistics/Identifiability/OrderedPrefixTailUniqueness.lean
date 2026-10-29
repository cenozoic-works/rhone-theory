/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteJointTailUniqueness
public import Mathlib.MeasureTheory.Measure.Real

/-! # An ordered pair law is determined by its prefix and tail masses -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability.ThreeSampleCDF

lemma tail_prefix_sum (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    μ.real (Ioi s ×ˢ Ioi t) + μ.real (Ioc 0 s ×ˢ Ioi t) =
      μ.real (Ioi 0 ×ˢ Ioi t) := by
  have hd : Disjoint (Ioi s ×ˢ Ioi t) (Ioc 0 s ×ˢ Ioi t) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hq.1.2) hp.1
  have he : (Ioi s ×ˢ Ioi t) ∪ (Ioc 0 s ×ˢ Ioi t) = Ioi 0 ×ˢ Ioi t := by
    ext p
    constructor
    · rintro (hp | hp)
      · exact ⟨hs.trans_lt hp.1, hp.2⟩
      · exact ⟨hp.1.1, hp.2⟩
    · intro hp
      by_cases hps : s < p.1
      · exact Or.inl ⟨hps, hp.2⟩
      · exact Or.inr ⟨⟨hp.1, le_of_not_gt hps⟩, hp.2⟩
  rw [← measureReal_union hd (measurableSet_Ioc.prod measurableSet_Ioi), he]

lemma ordered_tail_eq_first (μ : Measure (ℝ × ℝ))
    (ho : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) {s t : ℝ} (hst : t ≤ s) :
    μ.real (Ioi s ×ˢ Ioi t) = (μ.map Prod.fst).real (Ioi s) := by
  change μ.real (Ioi s ×ˢ Ioi t) = ((μ.map Prod.fst) (Ioi s)).toReal
  rw [Measure.map_apply measurable_fst measurableSet_Ioi]
  change μ.real (Ioi s ×ˢ Ioi t) = μ.real (Prod.fst ⁻¹' Ioi s)
  apply measureReal_congr
  filter_upwards [ho] with p hp
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, hst.trans_lt (h.trans hp.2)⟩⟩

lemma ordered_tail_replace_negative (μ : Measure (ℝ × ℝ))
    (ho : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) {s : ℝ} (hs : s ≤ 0) (t : ℝ) :
    μ.real (Ioi s ×ˢ Ioi t) = μ.real (Ioi 0 ×ˢ Ioi t) := by
  apply measureReal_congr
  filter_upwards [ho] with p hp
  apply propext
  exact ⟨fun h => ⟨hp.1, h.2⟩, fun h => ⟨hs.trans_lt hp.1, h.2⟩⟩

theorem eq_of_ordered_prefix_tail (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2)
    (hν : ∀ᵐ p ∂ν, 0 < p.1 ∧ p.1 < p.2)
    (hfirst : μ.map Prod.fst = ν.map Prod.fst)
    (hbox : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      μ.real (Ioc 0 s ×ˢ Ioi t) = ν.real (Ioc 0 s ×ˢ Ioi t)) : μ = ν := by
  have hpos (s t : ℝ) (hs : 0 ≤ s) :
      μ.real (Ioi s ×ˢ Ioi t) = ν.real (Ioi s ×ˢ Ioi t) := by
    by_cases hts : t ≤ s
    · rw [ordered_tail_eq_first μ hμ hts, ordered_tail_eq_first ν hν hts, hfirst]
    · have hst : s ≤ t := (lt_of_not_ge hts).le
      have ht := hs.trans hst
      have hμs := tail_prefix_sum μ hs t
      have hνs := tail_prefix_sum ν hs t
      have hμt := tail_prefix_sum μ ht t
      have hνt := tail_prefix_sum ν ht t
      rw [ordered_tail_eq_first μ hμ le_rfl, hfirst] at hμt
      rw [ordered_tail_eq_first ν hν le_rfl] at hνt
      rw [hbox s t hs hst] at hμs
      rw [hbox t t ht le_rfl] at hμt
      linarith
  apply eq_of_tail_rectangles
  intro s t
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change μ.real (Ioi s ×ˢ Ioi t) = ν.real (Ioi s ×ˢ Ioi t)
  by_cases hs : 0 ≤ s
  · exact hpos s t hs
  · rw [ordered_tail_replace_negative μ hμ (le_of_not_ge hs),
      ordered_tail_replace_negative ν hν (le_of_not_ge hs)]
    exact hpos 0 t le_rfl

end Rhone.Statistics.Identifiability.ThreeSampleCDF
