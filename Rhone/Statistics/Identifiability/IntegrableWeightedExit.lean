/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableTransitionStochastic
public import Rhone.Statistics.Identifiability.IntegrableProjectionDuhamel
public import Rhone.Statistics.Identifiability.FirstExit

/-! # Weighted first-exit flux and exact mass balance for locally-L1 finite generators -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.IntegrableWeightedExit
variable {n : ℕ}

def row (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (a t : ℝ) : Fin n → ℝ :=
  α ᵥ* inhomogeneousTransition Q a t

def survival (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (a t : ℝ) : ℝ :=
  ∑ i, row Q α a t i

def density (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (a t : ℝ) : ℝ :=
  dotProduct (row Q α a t) (exitRate (Q t))

def law (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi a)).withDensity (fun t => ENNReal.ofReal (density Q α a t))

lemma row_initial (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) : row Q α a a = α := by
  simp [row, integrableTransition_self Q hQ]

lemma survival_initial (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) :
    survival Q α a a = ∑ i, α i := by simp [survival, row_initial Q α hQ]

lemma row_continuous (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) (j : Fin n) :
    Continuous (fun t => row Q α a t j) := by
  have hc := integrableTransition_continuous Q hQ
  unfold row Matrix.vecMul dotProduct
  fun_prop

lemma survival_continuous (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) :
    Continuous (survival Q α a) :=
  continuous_finsetSum Finset.univ (fun j _ => row_continuous Q α hQ a j)

lemma row_ac (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b c : ℝ) (j : Fin n) :
    AbsolutelyContinuousOnInterval (fun t => row Q α a t j) b c :=
  finiteRowMatrixProduct_entry_ac (fun _ => α) (fun t => inhomogeneousTransition Q a t)
    b c (fun i => (LipschitzWith.const (α i)).lipschitzOnWith.absolutelyContinuousOnInterval)
    (integrableTransition_entry_ac_right Q hQ a b c) j

lemma row_derivative_ae (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) :
    ∀ᵐ t, ∀ j, HasDerivAt (fun s => row Q α a s j) ((row Q α a t ᵥ* Q t) j) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQ] with t ht j
  have hd := finiteRowMatrixProduct_hasDerivAt_at (fun _ => α)
    (fun s => inhomogeneousTransition Q a s) 0
    (inhomogeneousTransition Q a t * Q t) t (fun i => hasDerivAt_const t (α i))
    (ht a) j
  simpa only [Matrix.zero_vecMul, zero_add, row, Matrix.vecMul_vecMul] using hd

lemma survival_ac (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b c : ℝ) :
    AbsolutelyContinuousOnInterval (survival Q α a) b c :=
  ac_finset_sum Finset.univ (fun j _ => row_ac Q α hQ a b c j)

lemma survival_derivative_ae (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) :
    ∀ᵐ t, HasDerivAt (survival Q α a) (-density Q α a t) t := by
  filter_upwards [row_derivative_ae Q α hQ a] with t ht
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht j)
  convert! hd using 1
  simp only [density, exitRate, Matrix.mulVec, dotProduct, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib, neg_neg, Matrix.vecMul, Finset.mul_sum, mul_one]
  rw [Finset.sum_comm]

lemma exitRate_locallyIntegrable (Q : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (i : Fin n) :
    LocallyIntegrable (fun t => exitRate (Q t) i) volume := by
  have h := (locallyIntegrable_finsetSum Finset.univ (fun j _ => hQ i j)).neg
  convert! h using 1
  funext t
  simp only [exitRate, Pi.neg_apply, Matrix.mulVec, dotProduct, mul_one]

lemma density_locallyIntegrable (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a : ℝ) :
    LocallyIntegrable (density Q α a) volume :=
  locallyIntegrable_finsetSum Finset.univ fun i _ =>
    (exitRate_locallyIntegrable Q hQ i).continuous_mul (row_continuous Q α hQ a i)

lemma mass_balance (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b : ℝ) :
    (∫ t in a..b, density Q α a t) = (∑ i, α i) - survival Q α a b := by
  have he := ac_integral_eq_sub_ae (survival_ac Q α hQ a a b) (by
    filter_upwards [survival_derivative_ae Q α hQ a] with t ht _
    exact ht)
  rw [intervalIntegral.integral_neg, survival_initial Q α hQ a] at he
  linarith

end Rhone.Statistics.Identifiability.IntegrableWeightedExit
