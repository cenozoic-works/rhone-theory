/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.BivariateExponentialJetCriterion

/-! # Finite certificates for the literal alpha-exp(A s)-F-exp(B t)-v flux kernel -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def kernelValue (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (X : Matrix ι ι ℝ) (Y : Matrix κ κ ℝ) : ℝ :=
  dotProduct α (X *ᵥ (F *ᵥ (Y *ᵥ v)))

lemma kernelValue_add_left (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (X Z : Matrix ι ι ℝ) (Y : Matrix κ κ ℝ) :
    kernelValue α F v (X + Z) Y = kernelValue α F v X Y + kernelValue α F v Z Y := by
  simp only [kernelValue, Matrix.add_mulVec, dotProduct_add]

lemma kernelValue_add_right (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (X : Matrix ι ι ℝ) (Y Z : Matrix κ κ ℝ) :
    kernelValue α F v X (Y + Z) = kernelValue α F v X Y + kernelValue α F v X Z := by
  simp only [kernelValue, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]

lemma kernelValue_smul_left (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (r : ℝ) (X : Matrix ι ι ℝ) (Y : Matrix κ κ ℝ) :
    kernelValue α F v (r • X) Y = r * kernelValue α F v X Y := by
  simp only [kernelValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma kernelValue_smul_right (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (r : ℝ) (X : Matrix ι ι ℝ) (Y : Matrix κ κ ℝ) :
    kernelValue α F v X (r • Y) = r * kernelValue α F v X Y := by
  simp only [kernelValue, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

def kernelBilinear (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ) :
    Matrix ι ι ℝ →L[ℝ] (Matrix κ κ ℝ →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap
        { toFun := fun Y => kernelValue α F v X Y
          map_add' := fun Y Z => kernelValue_add_right α F v X Y Z
          map_smul' := by
            intro r Y
            exact kernelValue_smul_right α F v r X Y }
      map_add' := by
        intro X Z
        ext Y
        exact kernelValue_add_left α F v X Z Y
      map_smul' := by
        intro r X
        ext Y
        exact kernelValue_smul_left α F v r X Y }

@[simp] lemma kernelBilinear_apply (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ)
    (X : Matrix ι ι ℝ) (Y : Matrix κ κ ℝ) :
    kernelBilinear α F v X Y = kernelValue α F v X Y := rfl

theorem positive_kernel_zero_iff_finite [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) = 0) ↔
    (∀ i : ℕ, i < Fintype.card ι → ∀ j : ℕ, j < Fintype.card κ →
      kernelValue α F v (A ^ i) (B ^ j) = 0) := by
  simpa only [kernelBilinear_apply] using positive_bivariate_zero_iff_finite A B
    (kernelBilinear α F v)

end Rhone.Statistics.Identifiability.FiniteExponentialJets
