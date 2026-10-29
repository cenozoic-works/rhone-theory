/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.InhomogeneousMarkovFlow
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # A jointly continuous, two-parameter finite-dimensional evolution family -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def inhomogeneousFundamental (Q : ℝ → Matrix ι ι ℝ)
    (t : ℝ) : Matrix ι ι ℝ := by
  classical
  exact fun i => PeanoBaker.solution (fun t => inhomogeneousRowOperator (Q t))
    ((1 : Matrix ι ι ℝ) i) t

noncomputable def inhomogeneousFundamentalInverse (Q : ℝ → Matrix ι ι ℝ)
    (t : ℝ) : Matrix ι ι ℝ :=
  (inhomogeneousFundamental (fun t => -(Q t).transpose) t).transpose

@[simp] theorem inhomogeneousFundamental_zero (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    inhomogeneousFundamental Q 0 = 1 := by
  classical
  funext i
  exact PeanoBaker.solution_zero _ (inhomogeneousRowOperator_continuous Q hQ) _

theorem inhomogeneousFundamental_hasDerivAt (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (t : ℝ) (i j : ι) :
    HasDerivAt (fun s => inhomogeneousFundamental Q s i j)
      ((inhomogeneousFundamental Q t * Q t) i j) t := by
  classical
  exact (hasDerivAt_pi.mp (PeanoBaker.solution_hasDerivAt _
    (inhomogeneousRowOperator_continuous Q hQ) ((1 : Matrix ι ι ℝ) i) t)) j

theorem inhomogeneousFundamental_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    Continuous (inhomogeneousFundamental Q) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact continuous_iff_continuousAt.mpr fun t =>
    (inhomogeneousFundamental_hasDerivAt Q hQ t i j).continuousAt

@[simp] theorem inhomogeneousFundamentalInverse_zero (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    inhomogeneousFundamentalInverse Q 0 = 1 := by
  classical
  rw [inhomogeneousFundamentalInverse, inhomogeneousFundamental_zero]
  · exact Matrix.transpose_one
  · exact fun i j => (hQ j i).neg

theorem inhomogeneousFundamentalInverse_hasDerivAt (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (t : ℝ) (i j : ι) :
    HasDerivAt (fun s => inhomogeneousFundamentalInverse Q s i j)
      (-(Q t * inhomogeneousFundamentalInverse Q t) i j) t := by
  have h := inhomogeneousFundamental_hasDerivAt (fun t => -(Q t).transpose)
    (fun i j => (hQ j i).neg) t j i
  simpa only [inhomogeneousFundamentalInverse, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.neg_apply, mul_neg, ← Finset.sum_neg_distrib, mul_comm, neg_mul]
      using h

theorem inhomogeneousFundamentalInverse_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    Continuous (inhomogeneousFundamentalInverse Q) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact continuous_iff_continuousAt.mpr fun t =>
    (inhomogeneousFundamentalInverse_hasDerivAt Q hQ t i j).continuousAt

omit [DecidableEq ι] in
theorem finiteMatrixProduct_hasDerivAt (A B A' B' : ℝ → Matrix ι ι ℝ)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A' t i j) t)
    (hB : ∀ t i j, HasDerivAt (fun s => B s i j) (B' t i j) t)
    (t : ℝ) (i j : ι) :
    HasDerivAt (fun s => (A s * B s) i j)
      ((A' t * B t + A t * B' t) i j) t := by
  simpa only [Matrix.mul_apply, Matrix.add_apply, Pi.mul_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hA t i k).mul (hB t k j))

theorem inhomogeneousFundamental_mul_inverse (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (t : ℝ) :
    inhomogeneousFundamental Q t * inhomogeneousFundamentalInverse Q t = 1 := by
  classical
  have hd : ∀ t i j, HasDerivAt
      (fun s => (inhomogeneousFundamental Q s * inhomogeneousFundamentalInverse Q s) i j)
      0 t := by
    intro t i j
    have h := finiteMatrixProduct_hasDerivAt
      (inhomogeneousFundamental Q) (inhomogeneousFundamentalInverse Q)
      (fun s => inhomogeneousFundamental Q s * Q s)
      (fun s => -(Q s * inhomogeneousFundamentalInverse Q s))
      (inhomogeneousFundamental_hasDerivAt Q hQ)
      (inhomogeneousFundamentalInverse_hasDerivAt Q hQ) t i j
    simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply] using h
  ext i j
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s i j).differentiableAt)
    (fun s => (hd s i j).deriv) t 0
  simpa only [inhomogeneousFundamental_zero Q hQ,
    inhomogeneousFundamentalInverse_zero Q hQ, Matrix.one_mul] using hc

theorem inhomogeneousFundamentalInverse_mul (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (t : ℝ) :
    inhomogeneousFundamentalInverse Q t * inhomogeneousFundamental Q t = 1 := by
  classical
  exact mul_eq_one_comm.mp (inhomogeneousFundamental_mul_inverse Q hQ t)

noncomputable def inhomogeneousTransition (Q : ℝ → Matrix ι ι ℝ)
    (s t : ℝ) : Matrix ι ι ℝ :=
  inhomogeneousFundamentalInverse Q s * inhomogeneousFundamental Q t

@[simp] theorem inhomogeneousTransition_self (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s : ℝ) :
    inhomogeneousTransition Q s s = 1 :=
  inhomogeneousFundamentalInverse_mul Q hQ s

theorem inhomogeneousTransition_cocycle (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s u t : ℝ) :
    inhomogeneousTransition Q s t =
      inhomogeneousTransition Q s u * inhomogeneousTransition Q u t := by
  unfold inhomogeneousTransition
  symm
  calc
    _ = inhomogeneousFundamentalInverse Q s *
        ((inhomogeneousFundamental Q u * inhomogeneousFundamentalInverse Q u) *
          inhomogeneousFundamental Q t) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [inhomogeneousFundamental_mul_inverse Q hQ, Matrix.one_mul]

theorem inhomogeneousTransition_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    Continuous (fun p : ℝ × ℝ => inhomogeneousTransition Q p.1 p.2) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  unfold inhomogeneousTransition
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum; intro k _
  exact (((continuous_apply k).comp ((continuous_apply i).comp
    (inhomogeneousFundamentalInverse_continuous Q hQ))).comp continuous_fst).mul
    (((continuous_apply j).comp ((continuous_apply k).comp
      (inhomogeneousFundamental_continuous Q hQ))).comp continuous_snd)

theorem inhomogeneousTransition_hasDerivAt_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) (i j : ι) :
    HasDerivAt (fun u => inhomogeneousTransition Q s u i j)
      ((inhomogeneousTransition Q s t * Q t) i j) t := by
  have h := finiteMatrixProduct_hasDerivAt
    (fun _ => inhomogeneousFundamentalInverse Q s) (inhomogeneousFundamental Q)
    (fun _ => 0) (fun t => inhomogeneousFundamental Q t * Q t)
    (fun t i j => hasDerivAt_const t (inhomogeneousFundamentalInverse Q s i j))
    (inhomogeneousFundamental_hasDerivAt Q hQ) t i j
  simpa only [inhomogeneousTransition, Matrix.zero_mul, zero_add, Matrix.mul_assoc] using h

theorem inhomogeneousTransition_hasDerivAt_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) (i j : ι) :
    HasDerivAt (fun u => inhomogeneousTransition Q u t i j)
      (-(Q s * inhomogeneousTransition Q s t) i j) s := by
  have h := finiteMatrixProduct_hasDerivAt
    (inhomogeneousFundamentalInverse Q) (fun _ => inhomogeneousFundamental Q t)
    (fun s => -(Q s * inhomogeneousFundamentalInverse Q s)) (fun _ => 0)
    (inhomogeneousFundamentalInverse_hasDerivAt Q hQ)
    (fun s i j => hasDerivAt_const s (inhomogeneousFundamental Q t i j)) s i j
  simpa only [inhomogeneousTransition, Matrix.mul_zero, add_zero,
    Matrix.neg_mul, Matrix.mul_assoc, Matrix.neg_apply] using h

theorem inhomogeneousTransition_shift_hasDerivAt (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s u : ℝ) (i j : ι) :
    HasDerivAt (fun v => inhomogeneousTransition Q s (s + v) i j)
      (∑ k, inhomogeneousTransition Q s (s + u) i k * Q (s + u) k j) u := by
  simpa only [Matrix.mul_apply, mul_one, Function.comp_def] using
    (inhomogeneousTransition_hasDerivAt_right Q hQ s (s + u) i j).comp u
      ((hasDerivAt_id u).const_add s)

theorem inhomogeneousTransition_nonneg (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : ι) :
    0 ≤ inhomogeneousTransition Q s t i j := by
  have hn := inhomogeneous_row_solution_nonneg
    (fun u => Q (s + u)) (fun u => inhomogeneousTransition Q s (s + u) i)
    (fun k l => (hQc k l).comp (continuous_const.add continuous_id))
    (fun u hu => hQ (s + u) (add_nonneg hs hu))
    (fun u _ j => inhomogeneousTransition_shift_hasDerivAt Q hQc s u i j)
    (fun j => by simp [inhomogeneousTransition_self Q hQc, Matrix.one_apply]; split_ifs <;>
      norm_num)
  simpa only [add_sub_cancel] using hn (t - s) (sub_nonneg.mpr hst) j

theorem inhomogeneousTransition_row_sum_le_one (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    (∑ j, inhomogeneousTransition Q s t i j) ≤ 1 := by
  have hm := finiteRowODE_mass_le_initial
    (fun u => Q (s + u)) (fun u => inhomogeneousTransition Q s (s + u) i)
    (fun u _ j => inhomogeneousTransition_shift_hasDerivAt Q hQc s u i j)
    (fun u hu j => inhomogeneousTransition_nonneg Q hQc hQ hs (le_add_of_nonneg_right hu) i j)
    (fun u hu => hrows (s + u) (add_nonneg hs hu)) (sub_nonneg.mpr hst)
  simpa only [add_sub_cancel, add_zero, inhomogeneousTransition_self Q hQc,
    Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hm

theorem inhomogeneousTransition_row_sum_eq_one (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : ι) :
    (∑ j, inhomogeneousTransition Q s t i j) = 1 := by
  have hm := finiteRowODE_mass_eq_initial
    (fun u => Q (s + u)) (fun u => inhomogeneousTransition Q s (s + u) i)
    (fun u _ j => inhomogeneousTransition_shift_hasDerivAt Q hQc s u i j)
    (fun u hu => hrows (s + u) (add_nonneg hs hu)) (sub_nonneg.mpr hst)
  simpa only [add_sub_cancel, add_zero, inhomogeneousTransition_self Q hQc,
    Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hm

theorem inhomogeneousTransition_matrix_hasDerivAt_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) :
    HasDerivAt (inhomogeneousTransition Q s) (inhomogeneousTransition Q s t * Q t) t := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  exact inhomogeneousTransition_hasDerivAt_right Q hQ s t i j

theorem inhomogeneousTransition_matrix_hasDerivAt_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (s t : ℝ) :
    HasDerivAt (fun u => inhomogeneousTransition Q u t)
      (-(Q s * inhomogeneousTransition Q s t)) s := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  exact inhomogeneousTransition_hasDerivAt_left Q hQ s t i j

theorem exists_inhomogeneous_substochastic_transition (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) :
    ∃ U : ℝ → ℝ → Matrix ι ι ℝ,
      Continuous (fun p : ℝ × ℝ => U p.1 p.2) ∧
      (∀ s, U s s = 1) ∧
      (∀ s u t, U s t = U s u * U u t) ∧
      (∀ s t, HasDerivAt (U s) (U s t * Q t) t) ∧
      (∀ s t, HasDerivAt (fun u => U u t) (-(Q s * U s t)) s) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i j, 0 ≤ U s t i j) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i, (∑ j, U s t i j) ≤ 1) := by
  exact ⟨inhomogeneousTransition Q, inhomogeneousTransition_continuous Q hQc,
    inhomogeneousTransition_self Q hQc, inhomogeneousTransition_cocycle Q hQc,
    inhomogeneousTransition_matrix_hasDerivAt_right Q hQc,
    inhomogeneousTransition_matrix_hasDerivAt_left Q hQc,
    fun _ _ hs hst => inhomogeneousTransition_nonneg Q hQc hQ hs hst,
    fun _ _ hs hst => inhomogeneousTransition_row_sum_le_one Q hQc hQ hrows hs hst⟩

theorem exists_inhomogeneous_stochastic_transition (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0) :
    ∃ U : ℝ → ℝ → Matrix ι ι ℝ,
      Continuous (fun p : ℝ × ℝ => U p.1 p.2) ∧
      (∀ s, U s s = 1) ∧
      (∀ s u t, U s t = U s u * U u t) ∧
      (∀ s t, HasDerivAt (U s) (U s t * Q t) t) ∧
      (∀ s t, HasDerivAt (fun u => U u t) (-(Q s * U s t)) s) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i j, 0 ≤ U s t i j) ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ i, (∑ j, U s t i j) = 1) := by
  exact ⟨inhomogeneousTransition Q, inhomogeneousTransition_continuous Q hQc,
    inhomogeneousTransition_self Q hQc, inhomogeneousTransition_cocycle Q hQc,
    inhomogeneousTransition_matrix_hasDerivAt_right Q hQc,
    inhomogeneousTransition_matrix_hasDerivAt_left Q hQc,
    fun _ _ hs hst => inhomogeneousTransition_nonneg Q hQc hQ hs hst,
    fun _ _ hs hst => inhomogeneousTransition_row_sum_eq_one Q hQc hrows hs hst⟩

end Rhone.Statistics.Identifiability
