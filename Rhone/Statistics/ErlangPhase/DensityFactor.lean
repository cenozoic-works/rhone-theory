/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.Construction

/-! # Post-event density factor of the Erlang-phase model -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability FinitePhase FiniteExponentialJets
variable {J N : ℕ}

set_option backward.isDefEq.respectTransparency false

lemma post_exp (b t : ℝ) : NormedSpace.exp (t • post b) =
    Real.exp (-b * t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have he : t • post b = (-b * t) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    simp [post, hij, mul_comm]
  rw [he, exp_smul_identity]

lemma post_exit (b : ℝ) : exitRate (post b) = fun _ => b := by
  funext i
  simp [exitRate, Matrix.mulVec, dotProduct, post]

lemma density_factor (r w : Fin J → ℝ) (b s t : ℝ) :
    FinitePhase.density (pre (N := N) r) (flux r) (post b) (weights w) (s, t) =
      WeightedExit.density (pre (N := N) r) (weights w) s * (b * Real.exp (-b * (t - s))) := by
  rw [FinitePhase.density_matrix, post_exp, post_exit]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec]
  have hf : flux (N := N) r *ᵥ (fun _ => b) = b • exitRate (pre r) := by
    have he : (fun _ : Fin 1 => b) = b • (fun _ : Fin 1 => (1 : ℝ)) := by ext; simp
    rw [he, Matrix.mulVec_smul, flux_identity]
  simp only [← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp only [WeightedExit.density, flowOutput, pow_zero, Matrix.one_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Rhone.Statistics.ErlangPhase
