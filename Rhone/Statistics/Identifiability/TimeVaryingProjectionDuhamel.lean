/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow

/-! # Derivative of finite-row matrix products and a projected Duhamel formula -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem finiteRowMatrixProduct_hasDerivAt
    (x x' : ℝ → ι → ℝ) (A A' : ℝ → Matrix ι κ ℝ)
    (hx : ∀ t i, HasDerivAt (fun s => x s i) (x' t i) t)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A' t i j) t)
    (t : ℝ) (j : κ) :
    HasDerivAt (fun s => (x s ᵥ* A s) j)
      ((x' t ᵥ* A t + x t ᵥ* A' t) j) t := by
  simpa only [Matrix.vecMul, dotProduct, Pi.add_apply, Pi.mul_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx t i).mul (hA t i j))

theorem finiteRow_projection_duhamel
    (K : ℝ → Matrix κ κ ℝ) (hK : ∀ i j, Continuous (fun t => K t i j))
    (z e : ℝ → κ → ℝ) (he : Continuous e)
    (hz : ∀ t j, HasDerivAt (fun s => z s j) ((z t ᵥ* K t - e t) j) t)
    (t : ℝ) :
    z t + (fun j => ∫ s in (0 : ℝ)..t, (e s ᵥ* inhomogeneousTransition K s t) j) =
      z 0 ᵥ* inhomogeneousTransition K 0 t := by
  have hd (s : ℝ) (j : κ) :
      HasDerivAt (fun u => (z u ᵥ* inhomogeneousTransition K u t) j)
        (-(e s ᵥ* inhomogeneousTransition K s t) j) s := by
    have h := finiteRowMatrixProduct_hasDerivAt z
      (fun s => z s ᵥ* K s - e s) (fun s => inhomogeneousTransition K s t)
      (fun s => -(K s * inhomogeneousTransition K s t)) hz
      (fun s i j => inhomogeneousTransition_hasDerivAt_left K hK s t i j) s j
    convert h using 1
    simp only [Matrix.sub_vecMul, Matrix.vecMul_neg, Matrix.vecMul_vecMul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  have hcont (j : κ) : Continuous (fun s => (e s ᵥ* inhomogeneousTransition K s t) j) := by
    simp only [Matrix.vecMul, dotProduct]
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp he).mul
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((inhomogeneousTransition_continuous K hK).comp
          (continuous_id.prodMk continuous_const))))
  funext j
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s j) ((hcont j).neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg, inhomogeneousTransition_self K hK,
    Matrix.vecMul_one] at h
  change z t j + _ = _
  linarith

end Rhone.Statistics.Identifiability
