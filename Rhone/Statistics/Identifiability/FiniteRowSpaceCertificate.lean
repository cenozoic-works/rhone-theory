/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Tactic

/-! # Kernel annihilation is an explicit finite linear-system solvability condition -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

lemma finite_rowSpace_iff_annihilates_kernel (Q : Matrix ι ι ℝ) (α : ι → ℝ) :
    (∃ β : ι → ℝ, β ᵥ* Q = α) ↔ ∀ w : ι → ℝ, Q *ᵥ w = 0 → dotProduct α w = 0 := by
  classical
  constructor
  · rintro ⟨β, rfl⟩ w hw
    rw [← dotProduct_mulVec, hw, dotProduct_zero]
  · intro h
    let L : ι → (ι → ℝ) →ₗ[ℝ] ℝ := fun i => dotProductEquiv ℝ ι (Q i)
    let K : (ι → ℝ) →ₗ[ℝ] ℝ := dotProductEquiv ℝ ι α
    have hk : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker K := by
      intro w hw
      apply h w
      funext i
      exact ((Submodule.mem_iInf _).mp hw) i
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (FiniteDimensional.mem_span_of_iInf_ker_le_ker hk)
    refine ⟨β, ?_⟩
    funext j
    have he := LinearMap.congr_fun hβ (Pi.single j 1)
    simpa [L, K, Matrix.vecMul, dotProduct, Pi.single_apply] using he

end Rhone.Statistics.Identifiability
