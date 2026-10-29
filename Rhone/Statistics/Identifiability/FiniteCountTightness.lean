/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Sequences

/-! # Tightness from convergence of nonnegative vanishing count kernels -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Rhone.Statistics.Identifiability
namespace FiniteCountSeparation

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [PolishSpace E] [BorelSpace E]

omit [PolishSpace E] in
lemma measure_compl_le_of_integral (μ : ProbabilityMeasure E) (f : E →ᵇ ℝ)
    (hf : ∀ x, f x ≤ 1) {K : Set E} (hK : ∀ x ∉ K, f x ≤ 1 / 2) :
    (μ : Measure E) Kᶜ ≤ ENNReal.ofReal (2 * (1 - ∫ x, f x ∂μ)) := by
  have hi : Integrable (fun x => 2 * (1 - f x)) (μ : Measure E) :=
    ((integrable_const 1).sub (f.integrable μ)).const_mul 2
  have hnonneg : 0 ≤ᵐ[(μ : Measure E)] fun x => 2 * (1 - f x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (by norm_num) (sub_nonneg.mpr (hf x))
  have h := hi.measure_le_integral hnonneg (s := Kᶜ) (by
    intro x hx
    have hx' := hK x hx
    linarith)
  simpa only [integral_const_mul, integral_sub (integrable_const 1) (f.integrable μ),
    integral_const, probReal_univ, one_smul] using h

theorem isTight_of_vanishing_test_integrals
    (μ : ℕ → ProbabilityMeasure E) (target : ProbabilityMeasure E)
    (F : ℕ → E →ᵇ ℝ)
    (hFle : ∀ n x, F n x ≤ 1)
    (hvanish : ∀ n, Tendsto (F n) (cocompact E) (𝓝 0))
    (htarget : Tendsto (fun n => ∫ x, F n x ∂target) atTop (𝓝 1))
    (hconv : ∀ m, Tendsto (fun n => ∫ x, F m x ∂μ n) atTop
      (𝓝 (∫ x, F m x ∂target))) :
    IsTightMeasureSet (range fun n => (μ n : Measure E)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hδpos : 0 < δ := ENNReal.ofReal_pos.mp hδ
  have hm : ∀ᶠ m in atTop, 1 - δ / 4 < ∫ x, F m x ∂target :=
    htarget.eventually (eventually_gt_nhds (by linarith : 1 - δ / 4 < (1 : ℝ)))
  obtain ⟨m, hm⟩ := hm.exists
  have hn : ∀ᶠ n in atTop, 1 - δ / 2 < ∫ x, F m x ∂μ n :=
    (hconv m).eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn
  have hcocompact : {x : E | F m x < 1 / 2} ∈ cocompact E :=
    (hvanish m).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hcocompact
  have htail : ∀ n, N ≤ n → (μ n : Measure E) Kᶜ ≤ ENNReal.ofReal δ := by
    intro n hn
    calc
      (μ n : Measure E) Kᶜ ≤ ENNReal.ofReal (2 * (1 - ∫ x, F m x ∂μ n)) :=
        measure_compl_le_of_integral (μ n) (F m) (hFle m)
          (fun x hx => (hKsub hx).le)
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith [hN n hn])
  have hsingle (n : ℕ) : ∃ C : Set E, IsCompact C ∧
      (μ n : Measure E) Cᶜ ≤ ENNReal.ofReal δ := by
    have ht : IsTightMeasureSet {(μ n : Measure E)} := isTightMeasureSet_singleton
    obtain ⟨C, hC, hb⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht _ hδ
    exact ⟨C, hC, hb _ (mem_singleton _)⟩
  choose C hC hCmass using hsingle
  refine ⟨K ∪ ⋃ n ∈ Finset.range N, C n,
    hK.union ((Finset.range N).isCompact_biUnion fun n _ => hC n), ?_⟩
  rintro ν ⟨n, rfl⟩
  apply le_trans _ hδε.le
  by_cases hn : N ≤ n
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans (htail n hn)
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    apply (measure_mono (compl_subset_compl.mpr ?_)).trans (hCmass n)
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hmem, hx⟩⟩)

end FiniteCountSeparation
end Rhone.Statistics.Identifiability
