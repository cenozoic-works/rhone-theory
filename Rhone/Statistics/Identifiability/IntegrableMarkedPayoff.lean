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

def markedPayoffKernel (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (w : ι → ℝ) (i : ι) (p : ℝ × ℝ) : ℝ :=
  ((inhomogeneousTransition A 0 p.1 * M * inhomogeneousTransition B p.1 p.2) *ᵥ w) i

lemma markedPayoffKernel_continuous (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (w : ι → ℝ) (i : ι) :
    Continuous (markedPayoffKernel A B M w i) := by
  have hU := integrableTransition_continuous A hA
  have hV := integrableTransition_continuous B hB
  unfold markedPayoffKernel
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  fun_prop

lemma markedPayoffKernel_initial (A B : ℝ → Matrix ι ι ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (w : ι → ℝ) (i : ι) :
    markedPayoffKernel A B M w i (0,0) = (M *ᵥ w) i := by
  simp [markedPayoffKernel, integrableTransition_self A hA, integrableTransition_self B hB]

theorem integrable_marked_payoff (A B : ℝ → Matrix ι ι ℝ) (q : ℝ → ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hmark : ∀ u, A u - B u = q u • M) (w : ι → ℝ) (i : ι) (t : ℝ) :
    (inhomogeneousTransition A 0 t *ᵥ w) i -
      (inhomogeneousTransition B 0 t *ᵥ w) i =
        ∫ u in (0 : ℝ)..t, q u * markedPayoffKernel A B M w i (u,t) := by
  let F := fun u => (inhomogeneousTransition A 0 u * inhomogeneousTransition B u t) *ᵥ w
  have hac : AbsolutelyContinuousOnInterval (fun u => F u i) 0 t := by
    apply ac_finset_sum Finset.univ
    intro j _
    exact (finiteMatrixProduct_entry_ac _ _ 0 t
      (integrableTransition_entry_ac_right A hA 0 0 t)
      (integrableTransition_entry_ac_left B hB t 0 t) i j).fun_mul
      (LipschitzWith.const (w j)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : ∀ᵐ u, u ∈ uIcc (0 : ℝ) t →
      HasDerivAt (fun v => F v i) (q u * markedPayoffKernel A B M w i (u,t)) u := by
    filter_upwards [integrableTransition_interpolation_ae_hasDerivAt A B hA hB 0 t]
      with u hu _
    apply (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hu i j).mul_const (w j))).congr_deriv
    rw [hmark u]
    simp only [markedPayoffKernel, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hFTC := ac_integral_eq_sub_ae hac hd
  simpa only [F, integrableTransition_self A hA, integrableTransition_self B hB,
    Matrix.one_mul, Matrix.mul_one] using hFTC.symm

end Rhone.Statistics.Identifiability
