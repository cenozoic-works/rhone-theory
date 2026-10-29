/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.CompactMoments
public import Rhone.Statistics.ThreeSiteSeparator.SortedPairSupport
public import Rhone.Statistics.DependentPairedTest.MeasureBridge
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! # Compact sorted-iid candidate family -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator DependenceBudget DependentPairedTest

abbrev CompactTime := Icc (0 : ℝ) 1
abbrev CompactTriple := CompactTime × CompactTime × CompactTime
abbrev Selection := Fin 2 × Fin 3

def high (z : CompactTriple) : CompactTime :=
  ⟨max z.1.val (max z.2.1.val z.2.2.val),
    (sorted_coordinates_unit z.1.property z.2.1.property z.2.2.property).1⟩

def low (z : CompactTriple) : CompactTime :=
  ⟨min z.1.val (min z.2.1.val z.2.2.val),
    (sorted_coordinates_unit z.1.property z.2.1.property z.2.2.property).2.1⟩

def middle (z : CompactTriple) : CompactTime :=
  ⟨z.1.val + z.2.1.val + z.2.2.val - (high z).val - (low z).val,
    (sorted_coordinates_unit z.1.property z.2.1.property z.2.2.property).2.2⟩

theorem high_continuous : Continuous high := by
  unfold high
  fun_prop

theorem low_continuous : Continuous low := by
  unfold low
  fun_prop

theorem middle_continuous : Continuous middle := by
  unfold middle high low
  fun_prop

def selectEncoding (z : CompactTriple × Selection) : Cube 3 := fun i =>
  if i = z.2.2 then high z.1 else if z.2.1 = 0 then low z.1 else middle z.1

theorem select_encoding_continuous : Continuous selectEncoding := by
  apply continuous_prod_of_discrete_right.mpr
  intro s
  apply continuous_pi
  intro i
  change Continuous (fun t : CompactTriple =>
    if i = s.2 then high t else if s.1 = 0 then low t else middle t)
  by_cases hi : i = s.2
  · simpa only [hi, ite_true] using high_continuous
  · by_cases hb : s.1 = 0
    · simpa only [hi, ite_false, hb, ite_true] using low_continuous
    · simpa only [hi, ite_false, hb] using middle_continuous

def selectionLaw : Law Selection where
  mass _ := 1 / 6
  nonneg _ := by norm_num
  total := by norm_num [Fintype.card_prod]

def selectionProbability : ProbabilityMeasure Selection := ⟨lawMeasure selectionLaw, inferInstance⟩

def compactPan (μ : ProbabilityMeasure CompactTime) : ProbabilityMeasure (Cube 3) :=
  ((μ.prod (μ.prod μ)).prod selectionProbability).map selectEncoding

theorem compact_pan_continuous : Continuous compactPan := by
  have h2 : Continuous (fun μ : ProbabilityMeasure CompactTime => μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have h3 : Continuous (fun μ : ProbabilityMeasure CompactTime => μ.prod (μ.prod μ)) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk h2)
  exact (ProbabilityMeasure.continuous_map select_encoding_continuous).comp
    (ProbabilityMeasure.continuous_prod.comp (h3.prodMk continuous_const))

theorem compact_pan_range_compact : IsCompact (Set.range compactPan) :=
  isCompact_range compact_pan_continuous

theorem compact_pan_range_closed : IsClosed (Set.range compactPan) :=
  compact_pan_range_compact.isClosed

end Rhone.Statistics.WeakRegularSeparation
