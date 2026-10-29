/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableTwoParameterFlow
public import Rhone.Statistics.Identifiability.IntegrableClockCalculus

/-! # Variation of constants for locally integrable finite matrix histories -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix

namespace Rhone.Statistics.Identifiability

section RowProduct

variable {ι κ : Type*} [Fintype ι]

theorem finiteRowMatrixProduct_entry_ac (x : ℝ → ι → ℝ)
    (A : ℝ → Matrix ι κ ℝ) (a b : ℝ)
    (hx : ∀ i, AbsolutelyContinuousOnInterval (fun t => x t i) a b)
    (hA : ∀ i j, AbsolutelyContinuousOnInterval (fun t => A t i j) a b) (j : κ) :
    AbsolutelyContinuousOnInterval (fun t => (x t ᵥ* A t) j) a b := by
  exact ac_finset_sum Finset.univ fun i _ => (hx i).fun_mul (hA i j)

theorem finiteRowMatrixProduct_hasDerivAt_at (x : ℝ → ι → ℝ)
    (A : ℝ → Matrix ι κ ℝ) (x' : ι → ℝ) (A' : Matrix ι κ ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (x' i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (j : κ) :
    HasDerivAt (fun s => (x s ᵥ* A s) j)
      ((x' ᵥ* A t + x t ᵥ* A') j) t := by
  simpa only [Matrix.vecMul, dotProduct, Pi.add_apply, Pi.mul_apply,
    Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).mul (hA i j))

end RowProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteRow_integrable_transport_ae_hasDerivAt
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z e : ℝ → ι → ℝ) (a b t : ℝ)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s + e s) j) s) :
    ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => (z u ᵥ* inhomogeneousTransition Q u t) j)
        ((e s ᵥ* inhomogeneousTransition Q s t) j) s := by
  filter_upwards [hz, integrableTransition_ae_hasDerivAt_left Q hQ] with s hs hU hmem j
  have h := finiteRowMatrixProduct_hasDerivAt_at z
    (fun u => inhomogeneousTransition Q u t) (z s ᵥ* Q s + e s)
    (-(Q s * inhomogeneousTransition Q s t)) s (hs hmem) (hU t) j
  convert h using 1
  simp only [Matrix.add_vecMul, Matrix.vecMul_neg, Matrix.vecMul_vecMul,
    Pi.add_apply, Pi.neg_apply]
  ring

theorem finiteRow_integrable_transport_intervalIntegrable
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z e : ℝ → ι → ℝ) (a b t : ℝ)
    (hac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s + e s) j) s) (j : ι) :
    IntervalIntegrable (fun s => (e s ᵥ* inhomogeneousTransition Q s t) j) volume a b := by
  apply ac_intervalIntegrable_ae
    (finiteRowMatrixProduct_entry_ac z (fun s => inhomogeneousTransition Q s t)
      a b hac (integrableTransition_entry_ac_left Q hQ t a b) j)
  filter_upwards [finiteRow_integrable_transport_ae_hasDerivAt Q hQ z e a b t hz]
    with s hs hmem
  exact hs hmem j

theorem finiteRow_integrable_duhamel
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z e : ℝ → ι → ℝ) (a b : ℝ)
    (hac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s + e s) j) s) :
    z b = z a ᵥ* inhomogeneousTransition Q a b +
      (fun j => ∫ s in a..b, (e s ᵥ* inhomogeneousTransition Q s b) j) := by
  funext j
  have h := ac_integral_eq_sub_ae
    (finiteRowMatrixProduct_entry_ac z (fun s => inhomogeneousTransition Q s b)
      a b hac (integrableTransition_entry_ac_left Q hQ b a b) j)
    (by
      filter_upwards [finiteRow_integrable_transport_ae_hasDerivAt Q hQ z e a b b hz]
        with s hs hmem
      exact hs hmem j)
  rw [integrableTransition_self Q hQ, Matrix.vecMul_one] at h
  change z b j = _ + _
  linarith

theorem finiteRow_projection_duhamel_integrable
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z e : ℝ → ι → ℝ) (a b : ℝ)
    (hac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s - e s) j) s) :
    z b + (fun j => ∫ s in a..b, (e s ᵥ* inhomogeneousTransition Q s b) j) =
      z a ᵥ* inhomogeneousTransition Q a b := by
  have hz' : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s + -e s) j) s := by
    simpa only [sub_eq_add_neg] using hz
  have h := finiteRow_integrable_duhamel Q hQ z (fun s => -e s) a b hac hz'
  funext j
  have hj := congrFun h j
  simp only [Pi.add_apply, Matrix.neg_vecMul, Pi.neg_apply,
    intervalIntegral.integral_neg] at hj
  change z b j + _ = _
  linarith

theorem finiteRow_integrable_homogeneous_eq_transition
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z : ℝ → ι → ℝ) (a b : ℝ)
    (hac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s) j) s) :
    z b = z a ᵥ* inhomogeneousTransition Q a b := by
  have hz' : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s + (0 : ι → ℝ)) j) s := by
    simpa only [add_zero] using hz
  have h := finiteRow_integrable_duhamel Q hQ z (fun _ => 0) a b hac hz'
  funext j
  simpa using congrFun h j

omit [DecidableEq ι] in
theorem finiteRow_integrable_eq_of_initial_eq
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z w : ℝ → ι → ℝ) (a b : ℝ)
    (hzac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hwac : ∀ j, AbsolutelyContinuousOnInterval (fun s => w s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s) j) s)
    (hw : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => w u j) ((w s ᵥ* Q s) j) s)
    (hinit : z a = w a) : z b = w b := by
  classical
  rw [finiteRow_integrable_homogeneous_eq_transition Q hQ z a b hzac hz,
    finiteRow_integrable_homogeneous_eq_transition Q hQ w a b hwac hw, hinit]

omit [DecidableEq ι] in
theorem finiteRow_integrable_eqOn_of_initial_eq
    (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (z w : ℝ → ι → ℝ) (a b : ℝ)
    (hzac : ∀ j, AbsolutelyContinuousOnInterval (fun s => z s j) a b)
    (hwac : ∀ j, AbsolutelyContinuousOnInterval (fun s => w s j) a b)
    (hz : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => z u j) ((z s ᵥ* Q s) j) s)
    (hw : ∀ᵐ s, s ∈ uIcc a b → ∀ j,
      HasDerivAt (fun u => w u j) ((w s ᵥ* Q s) j) s)
    (hinit : z a = w a) : EqOn z w (uIcc a b) := by
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc (by simp) ht
  apply finiteRow_integrable_eq_of_initial_eq Q hQ z w a t
    (fun j => (hzac j).mono hsub) (fun j => (hwac j).mono hsub) _ _ hinit
  · filter_upwards [hz] with s hs hmem
    exact hs (hsub hmem)
  · filter_upwards [hw] with s hs hmem
    exact hs (hsub hmem)

end Rhone.Statistics.Identifiability
