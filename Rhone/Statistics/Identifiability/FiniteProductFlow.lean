/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow
public import Mathlib.Tactic

/-! # Product-state evolution and invariant-support certificates for finite row flows -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def productRowGenerator (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    Matrix (ι × κ) (ι × κ) ℝ := fun i j =>
  A i.1 j.1 * (if i.2 = j.2 then 1 else 0) +
    (if i.1 = j.1 then 1 else 0) * B i.2 j.2

noncomputable def tensorRow (x : ι → ℝ) (y : κ → ℝ) : ι × κ → ℝ :=
  fun i => x i.1 * y i.2

theorem tensorRow_productRowGenerator (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : κ → ℝ) (j : ι × κ) :
    (∑ i, tensorRow x y i * productRowGenerator A B i j) =
      (∑ i, x i * A i j.1) * y j.2 + x j.1 * (∑ i, y i * B i j.2) := by
  simp only [tensorRow, productRowGenerator, Fintype.sum_prod_type,
    mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · apply Finset.sum_congr rfl; intro i _; ring

theorem tensorRow_hasDerivAt (A : ℝ → Matrix ι ι ℝ) (B : ℝ → Matrix κ κ ℝ)
    (x : ℝ → ι → ℝ) (y : ℝ → κ → ℝ) (t : ℝ)
    (hx : ∀ j, HasDerivAt (fun u => x u j) (∑ i, x t i * A t i j) t)
    (hy : ∀ j, HasDerivAt (fun u => y u j) (∑ i, y t i * B t i j) t)
    (j : ι × κ) :
    HasDerivAt (fun u => tensorRow (x u) (y u) j)
      (∑ i, tensorRow (x t) (y t) i * productRowGenerator (A t) (B t) i j) t := by
  rw [tensorRow_productRowGenerator]
  exact (hx j.1).mul (hy j.2)

theorem finiteMatrix_solution_eq_transition (Q F : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s : ℝ)
    (hF : ∀ t i j, HasDerivAt (fun u => F u i j) ((F t * Q t) i j) t)
    (t : ℝ) : F t = F s * inhomogeneousTransition Q s t := by
  have hd : ∀ u i j, HasDerivAt
      (fun v => (F v * inhomogeneousTransition Q v s) i j) 0 u := by
    intro u i j
    have h := finiteMatrixProduct_hasDerivAt F (fun v => inhomogeneousTransition Q v s)
      (fun v => F v * Q v) (fun v => -(Q v * inhomogeneousTransition Q v s))
      hF (fun v => inhomogeneousTransition_hasDerivAt_left Q hQ v s) u i j
    simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply] using h
  have he : F t * inhomogeneousTransition Q t s = F s := by
    ext i j
    have h := is_const_of_deriv_eq_zero (fun v => (hd v i j).differentiableAt)
      (fun v => (hd v i j).deriv) t s
    simpa only [inhomogeneousTransition_self Q hQ, Matrix.mul_one] using h
  have h := congrArg (fun V => V * inhomogeneousTransition Q s t) he
  simpa only [Matrix.mul_assoc, ← inhomogeneousTransition_cocycle Q hQ,
    inhomogeneousTransition_self Q hQ, Matrix.mul_one] using h

omit [DecidableEq ι] in
theorem finiteRow_solution_eq_zero (Q : ℝ → Matrix ι ι ℝ) (v : ℝ → ι → ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hv : ∀ t j, HasDerivAt (fun u => v u j) (∑ i, v t i * Q t i j) t)
    (s : ℝ) (hzero : v s = 0) (t : ℝ) : v t = 0 := by
  classical
  let F : ℝ → Matrix ι ι ℝ := fun u _ j => v u j
  have hF : ∀ u i j, HasDerivAt (fun z => F z i j) ((F u * Q u) i j) u :=
    fun u _ j => hv u j
  have h := finiteMatrix_solution_eq_transition Q F hQ s hF t
  have hz : F s = 0 := by ext i j; exact congrFun hzero j
  rw [hz, Matrix.zero_mul] at h
  ext i
  exact congrFun (congrFun h i) i

theorem inhomogeneousTransition_zero_outside_closed (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (p : ι → Prop)
    (hclosed : ∀ t i j, p i → ¬p j → Q t i j = 0)
    (s t : ℝ) (i j : ι) (hi : p i) (hj : ¬p j) :
    inhomogeneousTransition Q s t i j = 0 := by
  classical
  let J := {j // ¬p j}
  let R : ℝ → Matrix J J ℝ := fun u a b => Q u a b
  let v : ℝ → J → ℝ := fun u a => inhomogeneousTransition Q s u i a
  have hR : ∀ a b, Continuous (fun u => R u a b) := fun a b => hQ a b
  have hv : ∀ u b, HasDerivAt (fun z => v z b) (∑ a, v u a * R u a b) u := by
    intro u b
    have he : (∑ a, inhomogeneousTransition Q s u i a * Q u a b) =
        ∑ a : J, v u a * R u a b := by
      rw [← Fintype.sum_subtype_add_sum_subtype p]
      have hz : (∑ a : {a // p a}, inhomogeneousTransition Q s u i a * Q u a b) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [hclosed u a b a.property b.property, mul_zero]
      rw [hz, zero_add]
    simpa only [Matrix.mul_apply, he] using inhomogeneousTransition_hasDerivAt_right Q hQ s u i b
  have hz : v s = 0 := by
    ext a
    have hia : i ≠ (a : ι) := fun h => a.property (h ▸ hi)
    simp [v, inhomogeneousTransition_self Q hQ, hia]
  exact congrFun (finiteRow_solution_eq_zero R v hR hv s hz t) ⟨j, hj⟩

theorem inhomogeneousTransition_mulVec_zero_of_closed (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (p : ι → Prop)
    (hclosed : ∀ t i j, p i → ¬p j → Q t i j = 0)
    (w : ι → ℝ) (hw : ∀ i, p i → w i = 0)
    (s t : ℝ) (i : ι) (hi : p i) :
    (inhomogeneousTransition Q s t *ᵥ w) i = 0 := by
  classical
  change (∑ j, inhomogeneousTransition Q s t i j * w j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j
  · rw [hw j hj, mul_zero]
  · rw [inhomogeneousTransition_zero_outside_closed Q hQ p hclosed s t i j hi hj, zero_mul]

theorem inhomogeneousTransition_product (A : ℝ → Matrix ι ι ℝ)
    (B : ℝ → Matrix κ κ ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j))
    (s t : ℝ) (i j : ι × κ) :
    inhomogeneousTransition (fun u => productRowGenerator (A u) (B u)) s t i j =
      inhomogeneousTransition A s t i.1 j.1 * inhomogeneousTransition B s t i.2 j.2 := by
  let Q := fun u => productRowGenerator (A u) (B u)
  let F : ℝ → Matrix (ι × κ) (ι × κ) ℝ := fun u a b =>
    inhomogeneousTransition A s u a.1 b.1 * inhomogeneousTransition B s u a.2 b.2
  have hQ : ∀ i j, Continuous (fun u => Q u i j) := by
    intro i j
    exact ((hA i.1 j.1).mul continuous_const).add (continuous_const.mul (hB i.2 j.2))
  have hF : ∀ u i j, HasDerivAt (fun v => F v i j) ((F u * Q u) i j) u := by
    intro u i j
    exact tensorRow_hasDerivAt A B (fun v => inhomogeneousTransition A s v i.1)
      (fun v => inhomogeneousTransition B s v i.2) u
      (inhomogeneousTransition_hasDerivAt_right A hA s u i.1)
      (inhomogeneousTransition_hasDerivAt_right B hB s u i.2) j
  have hFs : F s = 1 := by
    ext a b
    simp only [F, inhomogeneousTransition_self A hA, inhomogeneousTransition_self B hB,
      Matrix.one_apply]
    by_cases h₁ : a.1 = b.1 <;> by_cases h₂ : a.2 = b.2 <;>
      simp [h₁, h₂, Prod.ext_iff]
  have h := finiteMatrix_solution_eq_transition Q F hQ s hF t
  rw [hFs, Matrix.one_mul] at h
  exact congrFun (congrFun h.symm i) j

end Rhone.Statistics.Identifiability
