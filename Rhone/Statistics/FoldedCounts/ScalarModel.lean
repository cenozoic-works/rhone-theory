/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseCountLaw
public import Rhone.Statistics.Identifiability.ExponentialTwoEventLaw
public import Rhone.Statistics.Identifiability.ShearDensity

/-! # Scalar two-stage models for the folded three-sample counterexample -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.FoldedCounts
open MarkovChain.Identifiability Identifiability
open FiniteExponentialJets

def scalarModel (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : FinitePhase.Model 1 1 where
  A := fun _ _ => -a
  B := fun _ _ => -b
  F := fun _ _ => a
  N := !![-a, a; 0, -b]
  α := fun _ => 1
  A_metzler := by intro i j hij; exact (hij (Subsingleton.elim i j)).elim
  B_metzler := by intro i j hij; exact (hij (Subsingleton.elim i j)).elim
  N_metzler := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.of_apply, ha.le]
  A_rows := by intro i; simpa using ha.le
  B_rows := by intro i; simpa using hb.le
  N_rows := by intro i; fin_cases i <;> simp [Fin.sum_univ_two, hb.le]
  F_nonnegative := by intro i j; exact ha.le
  α_nonnegative := by intro i; norm_num
  α_sum := by simp
  flux := by ext i; simp [exitRate, Matrix.mulVec, dotProduct]
  pre_pre := by intro i j; fin_cases i; fin_cases j; rfl
  post_pre := by intro i j; fin_cases i; fin_cases j; rfl
  pre_post := by intro i j; fin_cases i; fin_cases j; rfl
  post_post := by intro i j; fin_cases i; fin_cases j; rfl
  exit_pre := by intro i; fin_cases i; simp [exitRate, dotProduct, Fin.sum_univ_two]
  exit_post := by intro i; fin_cases i; simp [exitRate, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma scalar_exp (a t : ℝ) (i j : Fin 1) :
    NormedSpace.exp (𝔸 := Matrix (Fin 1) (Fin 1) ℝ) (t • (fun _ _ : Fin 1 => -a)) i j =
      Real.exp (-a * t) := by
  have he : t • (fun _ _ : Fin 1 => -a) = (-a * t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext p q
    simp [Subsingleton.elim p q, mul_comm]
  rw [he, exp_smul_identity]
  simp [Subsingleton.elim i j]

lemma scalar_density (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (p : ℝ × ℝ) :
    (scalarModel a b ha hb).density p = ExponentialTwoEvent.density a b p := by
  have hA : (scalarModel a b ha hb).A = (-a) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [scalarModel, Subsingleton.elim i j]
  have hB : (scalarModel a b ha hb).B = (-b) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [scalarModel, Subsingleton.elim i j]
  unfold FinitePhase.Model.density FinitePhase.density orderedKernelDensity
  rw [hA, hB, smul_smul, smul_smul, exp_smul_identity, exp_smul_identity]
  simp [kernelValue, scalarModel, exitRate, Matrix.mulVec, dotProduct,
    ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity, mul_comm,
    mul_left_comm, mul_assoc]

lemma scalar_law (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (scalarModel a b ha hb).law = ExponentialTwoEvent.law a b := by
  unfold FinitePhase.Model.law FinitePhase.law ExponentialTwoEvent.law
  congr 1
  exact funext (scalar_density a b ha hb)

def source : FinitePhase.Model 1 1 := scalarModel (3 / 2) 2 (by norm_num) (by norm_num)

def comparator : FinitePhase.Model 1 1 := scalarModel 3 1 (by norm_num) (by norm_num)

lemma source_linear_system : ∃ β : Fin 2 → ℝ, β ᵥ* source.N = source.γ := by
  refine ⟨![-(2 / 3), -(1 / 2)], ?_⟩
  ext i
  fin_cases i <;>
    norm_num [source, scalarModel, FinitePhase.Model.γ, FinitePhase.initial,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.addCases]

lemma source_probability : IsProbabilityMeasure source.law :=
  source.probability_iff_linear_system.mpr source_linear_system

lemma comparator_probability : IsProbabilityMeasure comparator.law := by
  rw [comparator, scalar_law]
  exact ExponentialTwoEvent.law_probability (by norm_num) (by norm_num)

lemma source_origin_residual : source.densityResidual 0 0 = 9 / 4 := by
  have hd : source.density (0, 0) = 3 := by
    rw [source, scalar_density]
    norm_num [ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity]
  unfold FinitePhase.Model.densityResidual
  rw [hd]
  simp only [FinitePhase.Model.u, FinitePhase.Model.d, zero_smul,
    NormedSpace.exp_zero, Matrix.one_mulVec]
  norm_num [source, scalarModel, FinitePhase.Model.γ, FinitePhase.initial,
    FinitePhase.Model.h, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.addCases]

lemma source_not_certificate : ¬source.Certificate := by
  intro hc
  have h := hc 0 (by norm_num) 0 (by norm_num)
  simp only [pow_zero, kernelValue, Matrix.one_mulVec, tripleFlux_mulVec,
    dotProduct_smul] at h
  norm_num [source, scalarModel, tensorRow, FinitePhase.Model.γ, FinitePhase.initial,
    FinitePhase.Model.h, exitRate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.addCases] at h

theorem source_not_pan : ¬ThreeSampleMembership.PanRepresentable source.law := by
  intro hp
  exact source_not_certificate (source.pan_representable_iff_finite_algebra.mp hp).2

end Rhone.Statistics.FoldedCounts
