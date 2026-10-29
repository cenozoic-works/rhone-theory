/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeReferenceSkeleton
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Density of the indexed cut measure relative to branch counting and Lebesgue measure

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Set
open scoped ENNReal

noncomputable def indexedCutDensity {N : ℕ} (T : Tree N) (p : ℕ × ℝ) : ℝ≥0∞ := by
  classical
  exact if hb : p.1 < T.1 then
    if (T.2 ⟨p.1, hb⟩).1 ≠ ∅ ∧ (T.2 ⟨p.1, hb⟩).1 ≠ Finset.univ ∧
      p.2 ∈ Ioo (T.2 ⟨p.1, hb⟩).2.1 (T.2 ⟨p.1, hb⟩).2.2 then 1 else 0
    else 0

theorem indexedCutDensity_measurable {N : ℕ} (T : Tree N) :
    Measurable (indexedCutDensity T) := by
  classical
  apply measurable_from_prod_countable_right
  intro b
  by_cases hb : b < T.1
  · change Measurable (fun t : ℝ => indexedCutDensity T (b, t))
    simp only [indexedCutDensity, dite_eq_left hb]
    apply Measurable.ite _ measurable_const measurable_const
    exact (MeasurableSet.const ((T.2 ⟨b, hb⟩).1 ≠ ∅)).inter
      ((MeasurableSet.const ((T.2 ⟨b, hb⟩).1 ≠ Finset.univ)).inter
        (show MeasurableSet (Ioo (T.2 ⟨b, hb⟩).2.1 (T.2 ⟨b, hb⟩).2.2) from
          measurableSet_Ioo))
  · simp only [indexedCutDensity, dite_eq_right hb]
    exact measurable_const

theorem indexedTreeCutMeasure_flat {N : ℕ} (T : Tree N) :
    indexedTreeCutMeasure T =
      ((Measure.count : Measure ℕ).prod volume).withDensity (indexedCutDensity T) := by
  classical
  ext S hS
  let f (b : ℕ) := ∫⁻ t : ℝ, S.indicator (indexedCutDensity T) (b, t)
  rw [withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ ((indexedCutDensity_measurable T).indicator hS).aemeasurable,
    lintegral_count]
  change indexedTreeCutMeasure T S = ∑' b, f b
  rw [tsum_eq_sum (s := Finset.range T.1) (by
    intro b hb
    have hbt : ¬ b < T.1 := by simpa using hb
    simp [f, indexedCutDensity, hbt, Set.indicator])]
  rw [← Fin.sum_univ_eq_sum_range f T.1, indexedTreeCutMeasure, Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ
  · rcases hp with hp | hp <;>
      simp [indexedBranchCutMeasure, hp, f, indexedCutDensity, i.isLt, Set.indicator]
  · have hne : (T.2 i).1 ≠ ∅ ∧ (T.2 i).1 ≠ Finset.univ := not_or.mp hp
    have hm : Measurable (fun t : ℝ => (i.val, t)) :=
      measurable_const.prodMk measurable_id
    rw [indexedBranchCutMeasure, ite_eq_right hp,
      Measure.map_apply hm hS, Measure.restrict_apply (hS.preimage hm)]
    change volume ((fun t : ℝ => (i.val, t)) ⁻¹' S ∩
      Ioo (T.2 i).2.1 (T.2 i).2.2) = f i.val
    rw [← lintegral_indicator_one
      ((hS.preimage hm).inter measurableSet_Ioo)]
    apply lintegral_congr
    intro t
    by_cases hs : (i.val, t) ∈ S <;>
      by_cases ht : t ∈ Ioo (T.2 i).2.1 (T.2 i).2.2 <;>
      simp [indexedCutDensity, i.isLt, hne.1, hne.2, Set.indicator, hs, ht]

end Rhone.Coalescent.SmcPrime
