/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationFourEpochConvergence

/-! # Continuous differentiability of the four-epoch vector and its quiet-limit epochs -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel
open ContractiveDuhamel

theorem separated_mulVec_contDiff_one (E Q : ℝ → Mat) (v : Vec)
    (hE : ContDiff ℝ 1 E) (hQ : ContDiff ℝ 1 Q) :
    ContDiff ℝ 1 (fun x : ℝ × ℝ => E x.1 *ᵥ (Q x.2 *ᵥ v)) := by
  have h := (applyVec v).contDiff.comp
    ((hE.comp contDiff_fst).mul (hQ.comp contDiff_snd))
  simpa only [Function.comp_def, applyVec_apply, Matrix.mulVec_mulVec] using h

theorem quietEpoch_contDiff_one (ε δ r k : ℝ) :
    ContDiff ℝ 1 (fun t => quietEpoch t ε δ r k) := by
  have h := (contDiff_one_exp_affine (B δ r k) (0 : Mat)).comp
    (contDiff_id.sub (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => ε)))
  simpa only [Function.comp_def, quietEpoch, add_zero, id_eq] using h

theorem quietLimitEpoch_contDiff_one (r k : ℝ) :
    ContDiff ℝ 1 (fun t => quietLimitEpoch t r k) := by
  simpa only [quietLimitEpoch, add_zero] using contDiff_one_exp_affine (B 0 r k) (0 : Mat)

theorem fourEpochVector_contDiff_one (ε δ M r k : ℝ) (v : State → ℝ) :
    ContDiff ℝ 1 (fourEpochVector ε δ M r k v) :=
  separated_mulVec_contDiff_one _ _ _
    (early_pulse_contDiff_one ε δ r k) (quietEpoch_contDiff_one ε δ r k)

theorem idealVector_contDiff_one (r k : ℝ) : ContDiff ℝ 1 (idealVector r k) := by
  unfold idealVector
  exact separated_mulVec_contDiff_one (fun a => NormedSpace.exp (a • C))
    (fun t => quietLimitEpoch t r k) (fun _ => 1)
    (by simpa only [add_zero] using contDiff_one_exp_affine C (0 : Mat))
    (quietLimitEpoch_contDiff_one r k)

end Rhone.Statistics.Identifiability.MutationPulseKernel
