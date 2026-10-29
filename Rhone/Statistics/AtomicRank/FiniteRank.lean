/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.KernelLinearity
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Finite evaluation certificates for the all-degree conditional-kernel rank -/

@[expose] public section

noncomputable section
open Set
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

abbrev OpenUnitInterval := {z : ℝ // z ∈ Ioo (0 : ℝ) 1}

def IndependentModuloConstants {d : ℕ} (f : Fin d → Coefficients) : Prop :=
  ∀ (a : Fin d → ℝ) (c : ℝ),
    (∀ x y : ℝ, (∑ i, a i * value (f i) x y) = c) → ∀ i, a i = 0

def centeredKernel (n : ℕ) (f : Coefficients) (b : ℝ) (z : OpenUnitInterval) : ℝ :=
  uniformKernel (n + 1) (1 / ((n : ℝ) + 2)) f z.val - b

theorem centeredKernel_linearIndependent {n d : ℕ} (f : Fin d → Coefficients)
    (hf : ∀ i, DegreeBound (f i) n) (hi : IndependentModuloConstants f) (b : Fin d → ℝ) :
    LinearIndependent ℝ (fun i => centeredKernel n (f i) (b i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  let F := ∑ i, a i • f i
  have hF : DegreeBound F n := degreeBound_linear_combination a f hf
  have hc : ∀ z ∈ Ioo (0 : ℝ) 1,
      uniformKernel (n + 1) (1 / ((n : ℝ) + 2)) F z = ∑ i, a i * b i := by
    intro z hz
    have he := congrFun ha (⟨z, hz⟩ : OpenUnitInterval)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, centeredKernel] at he
    simp_rw [mul_sub] at he
    rw [Finset.sum_sub_distrib] at he
    rw [show F = ∑ i, a i • f i from rfl, uniformKernel_linear_combination]
    exact sub_eq_zero.mp he
  obtain ⟨c, hval⟩ := unit_interval_conditional_rigidity n F hF (∑ i, a i * b i) hc
  apply hi a c
  intro x y
  rw [← value_linear_combination]
  exact hval x y

theorem exists_full_rank_locations {n d : ℕ} (f : Fin d → Coefficients)
    (hf : ∀ i, DegreeBound (f i) n) (hi : IndependentModuloConstants f) (b : Fin d → ℝ) :
    ∃ z : Fin d → OpenUnitInterval,
      Matrix.det (fun i j : Fin d => centeredKernel n (f i) (b i) (z j)) ≠ 0 := by
  classical
  let H : OpenUnitInterval → Fin d → ℝ := fun z i => centeredKernel n (f i) (b i) z
  have hlin := centeredKernel_linearIndependent f hf hi b
  have hspan : Submodule.span ℝ (Set.range H) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hlin
  have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range H)) = d := by
    rw [hspan]
    simp
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range H)
  rw [hrank] at hex
  obtain ⟨v, hv, _, hvi⟩ := hex
  choose z hz using hv
  refine ⟨z, ?_⟩
  have hm : LinearIndependent ℝ (Matrix.col (fun i j : Fin d => H (z j) i)) := by
    change LinearIndependent ℝ (fun j => H (z j))
    have heq : (fun j => H (z j)) = v := funext hz
    rw [heq]
    exact hvi
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hm)).ne_zero

end Rhone.Statistics.AtomicRank
