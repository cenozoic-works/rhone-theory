/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteProductFlow
public import Rhone.Statistics.Identifiability.SingleMechanismPayoff

/-! # Exact restart and time-translation identities for continuous finite row flows -/

@[expose] public section

open Set
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inhomogeneousTransition_time_shift (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) :
    inhomogeneousTransition (fun u => Q (s + u)) 0 t =
      inhomogeneousTransition Q s (s + t) := by
  let A := fun u => Q (s + u)
  let F := fun u => inhomogeneousTransition Q s (s + u)
  have hA : ∀ i j, Continuous (fun u => A u i j) :=
    fun i j => (hQ i j).comp (continuous_const.add continuous_id)
  have hF : ∀ u i j, HasDerivAt (fun z => F z i j) ((F u * A u) i j) u :=
    fun u i j => inhomogeneousTransition_shift_hasDerivAt Q hQ s u i j
  have h := finiteMatrix_solution_eq_transition A F hA 0 hF t
  have h0 : F 0 = 1 := by simp only [F, add_zero, inhomogeneousTransition_self Q hQ]
  rw [h0, Matrix.one_mul] at h
  exact h.symm

theorem rowPayoff_restart (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s a t : ℝ) (i : ι) (v : ι → ℝ) :
    (inhomogeneousTransition Q s (a + t) *ᵥ v) i =
      rowPayoff (inhomogeneousTransition Q s a i)
        (inhomogeneousTransition (fun u => Q (a + u)) 0 t) v := by
  rw [inhomogeneousTransition_time_shift Q hQ,
    inhomogeneousTransition_cocycle Q hQ s a (a + t)]
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem inhomogeneousTransition_eq_of_eqOn (Q R : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hR : ∀ i j, Continuous (fun t => R t i j)) {s t : ℝ} (hst : s ≤ t)
    (heq : EqOn Q R (Icc s t)) :
    inhomogeneousTransition Q s t = inhomogeneousTransition R s t := by
  apply sub_eq_zero.mp
  rw [inhomogeneousTransition_sub_eq_integral Q R hQ hR]
  apply intervalIntegral.integral_zero_ae
  apply Filter.Eventually.of_forall
  intro u hu
  rw [uIoc_of_le hst] at hu
  rw [heq ⟨hu.1.le, hu.2⟩, sub_self, Matrix.mul_zero, Matrix.zero_mul]

end Rhone.Statistics.Identifiability
