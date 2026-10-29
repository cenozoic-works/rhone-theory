/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseKernel
public import Rhone.Statistics.Identifiability.IndependentClockObservation

/-!
# An explicit stationary reversible three-allele mutation channel with two unequal decay modes
-/

@[expose] public section

open Set MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Operator

noncomputable section
namespace Rhone.Statistics.Identifiability.ThreeAlleleMutation

abbrev State := Fin 3
abbrev MutationMatrix := Matrix State State ℝ

def Q : MutationMatrix := !![-3, 2, 1; 2, -3, 1; 1, 1, -2]

def generator (k : ℝ) : MutationMatrix := (k/2) • Q

def transition (k t : ℝ) : MutationMatrix := NormedSpace.exp (t • generator k)

def modeV : State → ℝ := ![1, -1, 0]
def modeW : State → ℝ := ![1, 1, -2]
def stationary : State → ℝ := fun _ => 1/3

lemma Q_metzler : IsMetzler Q := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Q] at *

lemma Q_conservative : IsConservative Q := by
  ext i
  fin_cases i <;> norm_num [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma Q_symmetric : Qᵀ = Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Q]

lemma Q_modeV : Q *ᵥ modeV = (-5 : ℝ) • modeV := by
  ext i
  fin_cases i <;> norm_num [Q, modeV, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma Q_modeW : Q *ᵥ modeW = (-3 : ℝ) • modeW := by
  ext i
  fin_cases i <;> norm_num [Q, modeW, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma stationary_sum : ∑ i, stationary i = 1 := by
  norm_num [stationary, Fin.sum_univ_succ]

lemma stationary_positive (i : State) : 0 < stationary i := by
  norm_num [stationary]

lemma detailed_balance (i j : State) : stationary i * Q i j = stationary j * Q j i := by
  have h := congrFun (congrFun Q_symmetric i) j
  simpa [stationary, Matrix.transpose_apply] using congrArg (fun x : ℝ => (1/3)*x) h.symm

lemma modeV_centered : ∑ i, stationary i * modeV i = 0 := by
  norm_num [stationary, modeV, Fin.sum_univ_succ]

lemma modeW_centered : ∑ i, stationary i * modeW i = 0 := by
  norm_num [stationary, modeW, Fin.sum_univ_succ]

lemma modeV_norm : ∑ i, stationary i * (modeV i)^2 = (2/3 : ℝ) := by
  norm_num [stationary, modeV, Fin.sum_univ_succ]

lemma modeW_norm : ∑ i, stationary i * (modeW i)^2 = (2 : ℝ) := by
  norm_num [stationary, modeW, Fin.sum_univ_succ]

lemma modes_orthogonal : ∑ i, stationary i * modeV i * modeW i = 0 := by
  norm_num [stationary, modeV, modeW, Fin.sum_univ_succ]

lemma generator_metzler {k : ℝ} (hk : 0 ≤ k) : IsMetzler (generator k) := by
  intro i j hij
  exact mul_nonneg (by positivity) (Q_metzler i j hij)

lemma generator_conservative (k : ℝ) : IsConservative (generator k) := by
  unfold IsConservative generator
  rw [Matrix.smul_mulVec, Q_conservative, smul_zero]

lemma transition_zero (k : ℝ) : transition k 0 = 1 := by
  simp [transition]

lemma transition_add (k s t : ℝ) : transition k (s+t) = transition k s * transition k t := by
  unfold transition
  rw [add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl (generator k)).smul_left s).smul_right t

lemma transition_transpose (k t : ℝ) : (transition k t)ᵀ = transition k t := by
  unfold transition generator
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, Matrix.transpose_smul, Q_symmetric]

lemma transition_symmetric (k t : ℝ) (i j : State) :
    transition k t i j = transition k t j i := by
  exact (congrFun (congrFun (transition_transpose k t) i) j).symm

lemma transition_nonneg {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) (i j : State) :
    0 ≤ transition k t i j := exp_generator_nonneg _ (generator_metzler hk) ht i j

lemma transition_row_sum (k t : ℝ) (i : State) : ∑ j, transition k t i j = 1 := by
  have h := congrFun (exp_generator_rows (generator k) (generator_conservative k) t) i
  simpa only [transition, Matrix.mulVec, dotProduct, mul_one] using h

lemma transition_column_sum (k t : ℝ) (i : State) : ∑ j, transition k t j i = 1 := by
  simp_rw [transition_symmetric k t _ i]
  exact transition_row_sum k t i

lemma stationary_invariant (k t : ℝ) (i : State) :
    ∑ j, stationary j * transition k t j i = stationary i := by
  simp only [stationary, ← Finset.mul_sum, transition_column_sum, mul_one]

lemma transition_measurable (k : ℝ) (i j : State) :
    Measurable (fun t => transition k t i j) := by
  have h := flowOutput_continuous (generator k) i (Pi.single j 1) 0
  change Continuous (fun t => flowOutput (generator k) i (Pi.single j 1) 0 t) at h
  simpa [flowOutput, transition, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
    using h.measurable

def ancestralPair (k t : ℝ) (i j : State) : ℝ :=
  ∑ root, stationary root * (transition k t root i * transition k t root j)

lemma ancestralPair_eq_double_transition (k t : ℝ) (i j : State) :
    ancestralPair k t i j = (1/3 : ℝ) * transition k (t+t) i j := by
  rw [transition_add, Matrix.mul_apply]
  unfold ancestralPair stationary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  rw [transition_symmetric k t root i]

theorem ancestralPair_eq_exp (k t : ℝ) (i j : State) :
    ancestralPair k t i j = (1/3 : ℝ) * NormedSpace.exp ((k*t) • Q) i j := by
  have hs : (t+t) • generator k = (k*t) • Q := by
    simp only [generator, smul_smul]
    congr 1
    ring
  simpa only [transition, hs] using ancestralPair_eq_double_transition k t i j

def siteKernel (k t : ℝ) (a : FiniteSiteObservation.AllelePair 3) : ℝ :=
  ancestralPair k t a.1 a.2

lemma siteKernel_nonneg {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (a : FiniteSiteObservation.AllelePair 3) : 0 ≤ siteKernel k t a := by
  unfold siteKernel ancestralPair
  apply Finset.sum_nonneg
  intro root _
  exact mul_nonneg (stationary_positive root).le
    (mul_nonneg (transition_nonneg hk ht root a.1) (transition_nonneg hk ht root a.2))

lemma siteKernel_sum (k t : ℝ) :
    ∑ a : FiniteSiteObservation.AllelePair 3, siteKernel k t a = 1 := by
  simp only [siteKernel, ancestralPair_eq_double_transition, Fintype.sum_prod_type,
    ← Finset.mul_sum, transition_row_sum]
  norm_num [Fin.sum_univ_succ]

lemma siteKernel_le_one {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (a : FiniteSiteObservation.AllelePair 3) : siteKernel k t a ≤ 1 := by
  rw [← siteKernel_sum k t]
  exact Finset.single_le_sum (fun b _ => siteKernel_nonneg hk ht b) (Finset.mem_univ a)

lemma siteKernel_measurable (k : ℝ) (a : FiniteSiteObservation.AllelePair 3) :
    Measurable (fun t => siteKernel k t a) := by
  unfold siteKernel ancestralPair
  apply Finset.measurable_sum
  intro root _
  exact measurable_const.mul ((transition_measurable k root a.1).mul
    (transition_measurable k root a.2))

lemma exp_mode {f : State → ℝ} {lambda : ℝ}
    (hf : Q *ᵥ f = (-lambda) • f) (u : ℝ) :
    NormedSpace.exp (u • Q) *ᵥ f = Real.exp (-lambda*u) • f := by
  apply MutationPulseKernel.exp_mulVec_eigen
  rw [Matrix.smul_mulVec, hf, smul_smul]
  congr 1
  ring

lemma siteKernel_contrast {f : State → ℝ} {lambda : ℝ}
    (hf : Q *ᵥ f = (-lambda) • f) (k t : ℝ) :
    ∑ a : FiniteSiteObservation.AllelePair 3, siteKernel k t a * (f a.1*f a.2) =
      (∑ i, stationary i * (f i)^2) * Real.exp (-(lambda*k)*t) := by
  simp only [siteKernel, ancestralPair_eq_exp, Fintype.sum_prod_type]
  have he := exp_mode hf (k*t)
  have hsum (i : State) :
      ∑ j, (1/3 : ℝ)*NormedSpace.exp ((k*t) • Q) i j*(f i*f j) =
        (1/3 : ℝ)*f i*(Real.exp (-lambda*(k*t))*f i) := by
    have hi := congrFun he i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    calc
      _ = ((1/3 : ℝ)*f i)*∑ j, NormedSpace.exp ((k*t) • Q) i j*f j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hi]
  simp_rw [hsum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [stationary]
  rw [show -lambda*(k*t) = -(lambda*k)*t by ring]
  ring

lemma siteKernel_contrastV (k t : ℝ) :
    ∑ a : FiniteSiteObservation.AllelePair 3,
      siteKernel k t a * (modeV a.1*modeV a.2) =
        (2/3 : ℝ)*Real.exp (-(5*k)*t) := by
  simpa only [modeV_norm] using siteKernel_contrast (lambda := 5) Q_modeV k t

lemma siteKernel_contrastW (k t : ℝ) :
    ∑ a : FiniteSiteObservation.AllelePair 3,
      siteKernel k t a * (modeW a.1*modeW a.2) =
        (2 : ℝ)*Real.exp (-(3*k)*t) := by
  simpa only [modeW_norm] using siteKernel_contrast (lambda := 3) Q_modeW k t

end Rhone.Statistics.Identifiability.ThreeAlleleMutation
