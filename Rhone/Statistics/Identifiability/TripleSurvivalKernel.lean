/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteProductExponential
public import Rhone.Statistics.Identifiability.BlockExponentialComparison

/-! # Finite linear realization of the three-sample pan density expression -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tripleGenerator (Q : Matrix ι ι ℝ) : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℝ :=
  productRowGenerator (productRowGenerator Q Q) Q

def tripleFlux (h d : ι → ℝ) : Matrix ((ι × ι) × ι) ι ℝ := fun i j =>
  3 * h i.1.1 * d i.1.2 * if i.2 = j then 1 else 0

lemma tripleFlux_mulVec (h d z : ι → ℝ) :
    tripleFlux h d *ᵥ z = 3 • tensorRow (tensorRow h d) z := by
  funext i
  simp [Matrix.mulVec, dotProduct, tripleFlux, tensorRow, mul_assoc]

lemma exp_add_time (Q : Matrix ι ι ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • Q) =
      NormedSpace.exp (s • Q) * NormedSpace.exp (t • Q) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl Q).smul_left s).smul_right t)

theorem triple_kernel_realization (Q : Matrix ι ι ℝ) (α h d : ι → ℝ) (s t : ℝ) :
    kernelValue (tensorRow (tensorRow α α) α) (tripleFlux h d) d
        (NormedSpace.exp (s • tripleGenerator Q)) (NormedSpace.exp (t • Q)) =
      3 * dotProduct α (NormedSpace.exp (s • Q) *ᵥ h) *
        dotProduct α (NormedSpace.exp (s • Q) *ᵥ d) *
        dotProduct α (NormedSpace.exp ((s + t) • Q) *ᵥ d) := by
  unfold kernelValue tripleGenerator
  rw [tripleFlux_mulVec, Matrix.mulVec_smul, dotProduct_smul]
  rw [tensor_flow_output, tensor_flow_output, exp_add_time, Matrix.mulVec_mulVec]
  ring

def scalarOutputLinear (α h : ι → ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => dotProduct α (X *ᵥ h)
      map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] }

lemma scalar_output_hasDerivAt (Q : Matrix ι ι ℝ) (α h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => dotProduct α (NormedSpace.exp (s • Q) *ᵥ h))
      (dotProduct α (NormedSpace.exp (t • Q) *ᵥ (Q *ᵥ h))) t := by
  have hd := (scalarOutputLinear α h).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const Q t)
  convert! hd using 1
  change dotProduct α (NormedSpace.exp (t • Q) *ᵥ (Q *ᵥ h)) =
      dotProduct α ((NormedSpace.exp (t • Q) * Q) *ᵥ h)
  rw [Matrix.mulVec_mulVec]

variable {κ η : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype η] [DecidableEq η] [Nonempty η]

theorem candidate_kernel_equal_iff_finite (A : Matrix κ κ ℝ) (B : Matrix η η ℝ)
    (α : κ → ℝ) (F : Matrix κ η ℝ) (v : η → ℝ)
    (Q : Matrix ι ι ℝ) (γ h : ι → ℝ) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) =
        3 * dotProduct γ (NormedSpace.exp (s • Q) *ᵥ h) *
          dotProduct γ (NormedSpace.exp (s • Q) *ᵥ (Q *ᵥ h)) *
          dotProduct γ (NormedSpace.exp ((s + t) • Q) *ᵥ (Q *ᵥ h))) ↔
    (∀ i : ℕ, i < Fintype.card κ + (Fintype.card ι * Fintype.card ι) * Fintype.card ι →
      ∀ j : ℕ, j < Fintype.card η + Fintype.card ι →
      kernelValue α F v (A ^ i) (B ^ j) =
        kernelValue (tensorRow (tensorRow γ γ) γ) (tripleFlux h (Q *ᵥ h)) (Q *ᵥ h)
          (tripleGenerator Q ^ i) (Q ^ j)) := by
  have he := positive_kernels_equal_iff_finite A B (tripleGenerator Q) Q
    α (tensorRow (tensorRow γ γ) γ) F (tripleFlux h (Q *ᵥ h)) v (Q *ᵥ h)
  simpa only [triple_kernel_realization, Fintype.card_prod] using he

end Rhone.Statistics.Identifiability.FiniteExponentialJets
