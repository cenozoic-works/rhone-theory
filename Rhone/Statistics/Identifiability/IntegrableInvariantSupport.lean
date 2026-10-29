/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableProjectionDuhamel

/-! # Invariant support for locally integrable finite matrix evolution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteMatrix_integrable_solution_eq_transition (Q F : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s t : ℝ)
    (hac : ∀ i j, AbsolutelyContinuousOnInterval (fun u => F u i j) s t)
    (hF : ∀ᵐ u, u ∈ uIcc s t → ∀ i j,
      HasDerivAt (fun v => F v i j) ((F u * Q u) i j) u) :
    F t = F s * inhomogeneousTransition Q s t := by
  ext i j
  have h := finiteRow_integrable_homogeneous_eq_transition Q hQ
    (fun u => F u i) s t (hac i) (by
      filter_upwards [hF] with u hu hmem j
      exact hu hmem i j)
  exact congrFun h j

omit [DecidableEq ι] in
theorem finiteRow_integrable_solution_eq_zero (Q : ℝ → Matrix ι ι ℝ)
    (v : ℝ → ι → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s t : ℝ)
    (hac : ∀ j, AbsolutelyContinuousOnInterval (fun u => v u j) s t)
    (hv : ∀ᵐ u, u ∈ uIcc s t → ∀ j,
      HasDerivAt (fun z => v z j) (∑ i, v u i * Q u i j) u)
    (hzero : v s = 0) : v t = 0 := by
  classical
  have h := finiteRow_integrable_homogeneous_eq_transition Q hQ v s t hac hv
  simpa only [hzero, Matrix.zero_vecMul] using h

theorem integrableTransition_zero_outside_closed_on_interval (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (p : ι → Prop)
    (s t : ℝ)
    (hclosed : ∀ᵐ u, u ∈ uIcc s t → ∀ i j, p i → ¬p j → Q u i j = 0)
    (i j : ι) (hi : p i) (hj : ¬p j) :
    inhomogeneousTransition Q s t i j = 0 := by
  classical
  let J := {j // ¬p j}
  let R : ℝ → Matrix J J ℝ := fun u a b => Q u a b
  let v : ℝ → J → ℝ := fun u a => inhomogeneousTransition Q s u i a
  have hR : ∀ a b, LocallyIntegrable (fun u => R u a b) volume := fun a b => hQ a b
  have hv : ∀ᵐ u, u ∈ uIcc s t → ∀ b,
      HasDerivAt (fun z => v z b) (∑ a, v u a * R u a b) u := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQ, hclosed]
      with u hu hcl hmem b
    have he : (∑ a, inhomogeneousTransition Q s u i a * Q u a b) =
        ∑ a : J, v u a * R u a b := by
      rw [← Fintype.sum_subtype_add_sum_subtype p]
      have hz : (∑ a : {a // p a}, inhomogeneousTransition Q s u i a * Q u a b) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [hcl hmem a b a.property b.property, mul_zero]
      rw [hz, zero_add]
    simpa only [Matrix.mul_apply, he] using hu s i b
  have hz : v s = 0 := by
    ext a
    have hia : i ≠ (a : ι) := fun h => a.property (h ▸ hi)
    simp [v, integrableTransition_self Q hQ, hia]
  exact congrFun (finiteRow_integrable_solution_eq_zero R v hR s t
    (fun a => integrableTransition_entry_ac_right Q hQ s s t i a) hv hz) ⟨j, hj⟩

theorem integrableTransition_zero_outside_closed (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (p : ι → Prop)
    (hclosed : ∀ᵐ u, ∀ i j, p i → ¬p j → Q u i j = 0)
    (s t : ℝ) (i j : ι) (hi : p i) (hj : ¬p j) :
    inhomogeneousTransition Q s t i j = 0 := by
  apply integrableTransition_zero_outside_closed_on_interval Q hQ p s t ?_ i j hi hj
  filter_upwards [hclosed] with u hu _
  exact hu

theorem integrableTransition_mulVec_zero_of_closed (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (p : ι → Prop)
    (hclosed : ∀ᵐ u, ∀ i j, p i → ¬p j → Q u i j = 0)
    (w : ι → ℝ) (hw : ∀ i, p i → w i = 0)
    (s t : ℝ) (i : ι) (hi : p i) :
    (inhomogeneousTransition Q s t *ᵥ w) i = 0 := by
  classical
  change (∑ j, inhomogeneousTransition Q s t i j * w j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j
  · rw [hw j hj, mul_zero]
  · rw [integrableTransition_zero_outside_closed Q hQ p hclosed s t i j hi hj, zero_mul]

end Rhone.Statistics.Identifiability
