/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableFlowStability

/-! # Transition matrices agree when locally integrable generators agree almost everywhere -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrableTransition_eq_of_ae_on_interval (Q R : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hR : ∀ i j, LocallyIntegrable (fun t => R t i j) volume) (s t : ℝ)
    (heq : ∀ᵐ u, u ∈ uIcc s t → Q u = R u) :
    inhomogeneousTransition Q s t = inhomogeneousTransition R s t := by
  ext i j
  apply sub_eq_zero.mp
  rw [integrableTransition_sub_eq_integral_entry Q R hQ hR]
  apply intervalIntegral.integral_zero_ae
  filter_upwards [heq] with u hu hmem
  rw [hu (uIoc_subset_uIcc hmem), sub_self, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end Rhone.Statistics.Identifiability
