/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Finite-dimensional compact moment uniqueness for observer mixtures -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace Rhone.Statistics.CollapsedGenealogy

abbrev Cube (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

def coordinate (d : ℕ) (i : Fin d) : Cube d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (x i).val, continuous_subtype_val.comp (continuous_apply i)⟩

def monomials (d : ℕ) : Submonoid (Cube d →ᵇ ℝ) where
  carrier := {f | ∃ n : Fin d → ℕ, f = ∏ i, coordinate d i ^ n i}
  one_mem' := ⟨fun _ => 0, by simp⟩
  mul_mem' := by
    rintro f g ⟨n, rfl⟩ ⟨m, rfl⟩
    refine ⟨fun i => n i + m i, ?_⟩
    simp only [pow_add, Finset.prod_mul_distrib]

def momentAlgebra (d : ℕ) : StarSubalgebra ℝ (Cube d →ᵇ ℝ) where
  toSubalgebra := Algebra.adjoin ℝ (monomials d : Set (Cube d →ᵇ ℝ))
  star_mem' := by
    intro f hf
    have he : star f = f := by ext x; simp
    rwa [he]

theorem moment_algebra_separates (d : ℕ) :
    ((momentAlgebra d).map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, (x i).val ≠ (y i).val := by
    by_contra hn
    push Not at hn
    exact hxy (funext fun i => Subtype.ext (hn i))
  refine ⟨(coordinate d i : Cube d → ℝ), ?_, hi⟩
  refine ⟨(coordinate d i).toContinuousMap, ?_, rfl⟩
  refine ⟨coordinate d i, Algebra.subset_adjoin ?_, rfl⟩
  refine ⟨fun j => if j = i then 1 else 0, ?_⟩
  simp

theorem compact_moment_unique (d : ℕ) (μ ν : Measure (Cube d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : Fin d → ℕ,
      (∫ x, ∏ i, (x i).val ^ n i ∂μ) = ∫ x, ∏ i, (x i).val ^ n i ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (moment_algebra_separates d)
  intro f hf
  change f ∈ (Algebra.adjoin ℝ (monomials d : Set (Cube d →ᵇ ℝ))).toSubmodule at hf
  rw [Algebra.adjoin_eq_span, Submonoid.closure_eq] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, rfl⟩ := hf
    simpa [coordinate] using hm n
  | zero => simp
  | add f g hf hg ihf ihg =>
    simp only [BoundedContinuousFunction.add_apply,
      integral_add (f.integrable μ) (g.integrable μ),
      integral_add (f.integrable ν) (g.integrable ν), ihf, ihg]
  | smul c f hf ih =>
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul, ih]

theorem compact_word_moment_unique (d : ℕ) (μ ν : Measure (Cube d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ (L : ℕ) (word : Fin L → Fin d),
      (∫ x, ∏ j, (x (word j)).val ∂μ) = ∫ x, ∏ j, (x (word j)).val ∂ν) : μ = ν := by
  classical
  apply compact_moment_unique d μ ν
  intro n
  let S := Σ i : Fin d, Fin (n i)
  let e := Fintype.equivFin S
  have he (x : Cube d) :
      (∏ j : Fin (Fintype.card S), (x (e.symm j).1).val) = ∏ i, (x i).val ^ n i := by
    rw [← e.prod_comp (fun j => (x (e.symm j).1).val)]
    simp [S, Fintype.prod_sigma]
  simpa only [he] using hm (Fintype.card S) (fun j => (e.symm j).1)

end Rhone.Statistics.CollapsedGenealogy
