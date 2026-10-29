/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TripleSurvivalKernel
public import Rhone.Statistics.Identifiability.DensityMarginals

/-! # Continuous ordered-time densities from finite matrix kernels -/

@[expose] public section

noncomputable section
open Set MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def orderedKernelDensity (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ) (p : ℝ × ℝ) : ℝ :=
  kernelValue α F v (NormedSpace.exp (p.1 • A)) (NormedSpace.exp ((p.2 - p.1) • B))

lemma matrix_exp_time_continuous (A : Matrix ι ι ℝ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • A)) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const A t).continuousAt

lemma orderedKernelDensity_continuous (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ) :
    Continuous (orderedKernelDensity A B α F v) := by
  have hA : Continuous (fun p : ℝ × ℝ => NormedSpace.exp (p.1 • A)) :=
    (matrix_exp_time_continuous A).comp continuous_fst
  have hB : Continuous (fun p : ℝ × ℝ => NormedSpace.exp ((p.2 - p.1) • B)) :=
    (matrix_exp_time_continuous B).comp (continuous_snd.sub continuous_fst)
  exact ((kernelBilinear α F v).continuous.comp hA).clm_apply hB

lemma orderedKernelDensity_duration (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (α : ι → ℝ) (F : Matrix ι κ ℝ) (v : κ → ℝ) (s t : ℝ) :
    orderedKernelDensity A B α F v (s,s + t) =
      kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) := by
  simp [orderedKernelDensity]

lemma orderedKernelDensity_nonnegative {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (α : Fin n → ℝ) (F : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ)
    (hA : IsMetzler A) (hB : IsMetzler B) (hα : ∀ i, 0 ≤ α i)
    (hF : ∀ i j, 0 ≤ F i j) (hv : ∀ i, 0 ≤ v i)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) : 0 ≤ orderedKernelDensity A B α F v p := by
  unfold orderedKernelDensity kernelValue
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hα i)
  apply matrix_mulVec_nonneg _ _ (exp_generator_nonneg A hA hp.1.le)
  intro a
  apply matrix_mulVec_nonneg _ _ hF
  exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg B hB (sub_nonneg.mpr hp.2.le)) hv

end Rhone.Statistics.Identifiability.FiniteExponentialJets
