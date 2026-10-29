/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableFlowStability
public import Rhone.Statistics.Identifiability.IntegrableInvariantSupport

/-! # An exact marked Duhamel payoff for locally integrable coefficient histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def markedPayoffKernelFrom (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (a : ℝ) (w : ι → ℝ) (i : ι) (p : ℝ × ℝ) : ℝ :=
  ((inhomogeneousTransition A a p.1 * M * inhomogeneousTransition B p.1 p.2) *ᵥ w) i

lemma markedPayoffKernelFrom_continuous (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (a : ℝ) (w : ι → ℝ) (i : ι) :
    Continuous (markedPayoffKernelFrom A B M a w i) := by
  have hU := integrableTransition_continuous A hA
  have hV := integrableTransition_continuous B hB
  unfold markedPayoffKernelFrom
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  fun_prop

lemma markedPayoffKernelFrom_initial (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (a : ℝ) (w : ι → ℝ) (i : ι) :
    markedPayoffKernelFrom A B M a w i (a,a) = (M *ᵥ w) i := by
  simp [markedPayoffKernelFrom, integrableTransition_self A hA, integrableTransition_self B hB]

theorem integrable_marked_payoff_from (A B : ℝ → Matrix ι ι ℝ) (q : ℝ → ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hmark : ∀ u, A u - B u = q u • M) (a : ℝ) (w : ι → ℝ) (i : ι) (t : ℝ) :
    (inhomogeneousTransition A a t *ᵥ w) i -
      (inhomogeneousTransition B a t *ᵥ w) i =
        ∫ u in a..t, q u * markedPayoffKernelFrom A B M a w i (u,t) := by
  let F := fun u => (inhomogeneousTransition A a u * inhomogeneousTransition B u t) *ᵥ w
  have hac : AbsolutelyContinuousOnInterval (fun u => F u i) a t := by
    apply ac_finset_sum Finset.univ
    intro j _
    exact (finiteMatrixProduct_entry_ac _ _ a t
      (integrableTransition_entry_ac_right A hA a a t)
      (integrableTransition_entry_ac_left B hB t a t) i j).fun_mul
      (LipschitzWith.const (w j)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : ∀ᵐ u, u ∈ uIcc a t →
      HasDerivAt (fun v => F v i) (q u * markedPayoffKernelFrom A B M a w i (u,t)) u := by
    filter_upwards [integrableTransition_interpolation_ae_hasDerivAt A B hA hB a t]
      with u hu _
    apply (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hu i j).mul_const (w j))).congr_deriv
    rw [hmark u]
    simp only [markedPayoffKernelFrom, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hFTC := ac_integral_eq_sub_ae hac hd
  simpa only [F, integrableTransition_self A hA, integrableTransition_self B hB,
    Matrix.one_mul, Matrix.mul_one] using hFTC.symm

end Rhone.Statistics.Identifiability
