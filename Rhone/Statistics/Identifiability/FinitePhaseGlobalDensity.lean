/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseMembership

/-! # Global density of a finite-phase model is determined by finitely many kernel values -/

@[expose] public section

noncomputable section
open Matrix Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ ι' κ' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

lemma global_kernels_equal_of_finite
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (A' : Matrix ι' ι' ℝ) (B' : Matrix κ' κ' ℝ)
    (α : ι → ℝ) (β : ι' → ℝ) (F : Matrix ι κ ℝ) (G : Matrix ι' κ' ℝ)
    (v : κ → ℝ) (w : κ' → ℝ)
    (h : ∀ i : ℕ, i < Fintype.card ι + Fintype.card ι' →
      ∀ j : ℕ, j < Fintype.card κ + Fintype.card κ' →
      kernelValue α F v (A ^ i) (B ^ j) = kernelValue β G w (A' ^ i) (B' ^ j))
    (s t : ℝ) :
    kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) =
      kernelValue β G w (NormedSpace.exp (s • A')) (NormedSpace.exp (t • B')) := by
  have hh : ∀ i : ℕ, i < Fintype.card (ι ⊕ ι') →
      ∀ j : ℕ, j < Fintype.card (κ ⊕ κ') →
      kernelBilinear (Sum.elim α (-β)) (Matrix.fromBlocks F 0 0 G) (Sum.elim v w)
        (Matrix.fromBlocks A 0 0 A' ^ i) (Matrix.fromBlocks B 0 0 B' ^ j) = 0 := by
    simpa only [kernelBilinear_apply, Matrix.fromBlocks_diagonal_pow,
      kernel_block_difference, sub_eq_zero, Fintype.card_sum] using h
  have hz := bivariate_zero_of_finite (Matrix.fromBlocks A 0 0 A')
    (Matrix.fromBlocks B 0 0 B')
    (kernelBilinear (Sum.elim α (-β)) (Matrix.fromBlocks F 0 0 G) (Sum.elim v w)) hh s t
  simpa only [kernelBilinear_apply, exp_fromBlocks_diagonal,
    kernel_block_difference, sub_eq_zero] using hz

end Rhone.Statistics.Identifiability.FiniteExponentialJets

namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open FiniteExponentialJets
variable {n m : ℕ} [NeZero n] [NeZero m]

lemma certificate_global_density (M : Model n m) (hc : M.Certificate) (s t : ℝ) :
    M.density (s, t) = 3 * M.u s * M.d s * M.d t := by
  have h := global_kernels_equal_of_finite M.A M.B (tripleGenerator M.N) M.N
    M.α (tensorRow (tensorRow M.γ M.γ) M.γ) M.F (tripleFlux M.h (M.N *ᵥ M.h))
    (exitRate M.B) (M.N *ᵥ M.h) (by
      simpa only [Certificate, Fintype.card_fin, Fintype.card_prod] using hc) s (t - s)
  rw [triple_kernel_realization, show s + (t - s) = t by ring] at h
  simpa only [density, FinitePhase.density, orderedKernelDensity, u, d] using h

end Rhone.Statistics.Identifiability.FinitePhase.Model
