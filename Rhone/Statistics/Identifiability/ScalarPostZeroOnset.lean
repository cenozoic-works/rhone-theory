/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseGlobalDensity

/-! # A scalar finite-phase model with zero onset is not pan representable -/

@[expose] public section

noncomputable section
open Set MeasureTheory Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open FiniteExponentialJets ThreeSampleMembership
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma scalar_post_density_factor (M : Model n 1) (s t : ℝ) :
    M.density (s, t) = Real.exp (t * M.B 0 0) * M.density (s, 0) := by
  have hb : M.B = (M.B 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp
  unfold density FinitePhase.density orderedKernelDensity
  rw [hb]
  simp only [smul_smul, exp_smul_identity, kernelValue_smul_right, zero_sub]
  rw [show (t - s) * M.B 0 0 = t * M.B 0 0 + (-s) * M.B 0 0 by ring,
    Real.exp_add]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true, mul_one]
  ring

theorem not_pan_of_scalar_post_zero_onset (M : Model n 1)
    [IsProbabilityMeasure M.law] (hd : M.d 0 = 0) : ¬PanRepresentable M.law := by
  intro hp
  have hc := M.pan_representable_iff_certificate.mp hp
  have hz (s : ℝ) : M.density (s, 0) = 0 := by
    rw [M.certificate_global_density hc, hd, mul_zero]
  have hall : M.density = fun _ => 0 := by
    funext p
    rcases p with ⟨s, t⟩
    rw [M.scalar_post_density_factor, hz, mul_zero]
  have hl : M.law = 0 := by
    change triangularDensityLaw M.density = 0
    rw [hall]
    simp [triangularDensityLaw]
  have hm : M.law univ = 1 := measure_univ
  rw [hl] at hm
  simp at hm

end Rhone.Statistics.Identifiability.FinitePhase.Model
