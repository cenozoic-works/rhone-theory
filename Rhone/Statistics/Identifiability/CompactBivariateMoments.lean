/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Uniqueness of compact bivariate moments -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace Rhone.Statistics.Identifiability

abbrev CompactMomentSquare := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

def firstCoordinate : CompactMomentSquare →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val,
    continuous_subtype_val.comp continuous_fst⟩

def secondCoordinate : CompactMomentSquare →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => x.2.val,
    continuous_subtype_val.comp continuous_snd⟩

def coordinateMonomials : Submonoid (CompactMomentSquare →ᵇ ℝ) where
  carrier := {f | ∃ m n : ℕ, f = firstCoordinate ^ m * secondCoordinate ^ n}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro f g ⟨m, n, rfl⟩ ⟨p, q, rfl⟩
    exact ⟨m + p, n + q, by simp [pow_add]; ring⟩

def coordinateAlgebra : StarSubalgebra ℝ (CompactMomentSquare →ᵇ ℝ) where
  toSubalgebra := Algebra.adjoin ℝ (coordinateMonomials : Set (CompactMomentSquare →ᵇ ℝ))
  star_mem' := by
    intro f hf
    have hstar : star f = f := by ext x; simp
    rwa [hstar]

theorem coordinateAlgebra_separates :
    (coordinateAlgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  by_cases hfirst : x.1.val = y.1.val
  · refine ⟨(secondCoordinate : CompactMomentSquare → ℝ), ?_, ?_⟩
    · refine ⟨secondCoordinate.toContinuousMap, ?_, rfl⟩
      exact ⟨secondCoordinate, Algebra.subset_adjoin ⟨0, 1, by simp⟩, rfl⟩
    · change x.2.val ≠ y.2.val
      intro hsecond
      apply hxy
      exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)
  · refine ⟨(firstCoordinate : CompactMomentSquare → ℝ), ?_, ?_⟩
    · refine ⟨firstCoordinate.toContinuousMap, ?_, rfl⟩
      exact ⟨firstCoordinate, Algebra.subset_adjoin ⟨1, 0, by simp⟩, rfl⟩
    · exact hfirst

theorem compact_bivariate_moment_unique
    (μ ν : Measure CompactMomentSquare) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ m n : ℕ,
      (∫ x, x.1.val ^ m * x.2.val ^ n ∂μ) =
        ∫ x, x.1.val ^ m * x.2.val ^ n ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    coordinateAlgebra_separates
  intro f hf
  change f ∈ (Algebra.adjoin ℝ
    (coordinateMonomials : Set (CompactMomentSquare →ᵇ ℝ))).toSubmodule at hf
  rw [Algebra.adjoin_eq_span, Submonoid.closure_eq] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, n, rfl⟩ := hf
    simpa [firstCoordinate, secondCoordinate] using hmom m n
  | zero => simp
  | add f g hf hg ihf ihg =>
    simp only [BoundedContinuousFunction.add_apply,
      integral_add (f.integrable μ) (g.integrable μ),
      integral_add (f.integrable ν) (g.integrable ν), ihf, ihg]
  | smul r f hf ih =>
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul,
      integral_const_mul, ih]

end Rhone.Statistics.Identifiability
