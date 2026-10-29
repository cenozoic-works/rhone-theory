/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.MarginalLumping.LengthB

/-! # `E[L_A · L_B]` for the unkilled graph: the `B`-side hypothesis discharged -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def CovAB (t : TS n KA KB) : Prop :=
  WF t.st.1 ∧ coverA t.st.1 = Finset.univ ∧ coverB t.st.1 = Finset.univ

theorem covAB_initT : CovAB (⟨initT n KA KB⟩ : TS n KA KB) :=
  ⟨fullState_wf, coverA_fullState, coverB_fullState⟩

theorem uBlkB_step_covAB (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hCt : CovAB t) :
    uBlkB t = holdB (0 : ℝ) 0 ρ (cladeFam n) t
      + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlkB t' := by
  rw [holdB, ← rBlkB_eq_rB hCt.1 hCt.2.2]
  exact uBlkB_step h hCt.1

theorem uBlk_step_covAB (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hCt : CovAB t) :
    uBlk t = holdA (0 : ℝ) 0 ρ (cladeFam n) t
      + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t' := by
  rw [holdA, ← rBlk_eq_rA hCt.1 hCt.2.1]
  exact uBlk_step h hCt.1

theorem expected_LA_LB_eq_of_secondMoment (h : Adm (0 : ℝ) 0 ρ πA πB)
    {w : TS n KA KB → ℝ}
    (hfw : ∀ t : TS n KA KB, CovAB t →
      w t = (holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlkB t
          + holdB (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t)
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t')
    {s : TS n KA KB}
    (hlw : Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N w s) Filter.atTop (nhds 0))
    (hCs : CovAB s) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
          ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
            * holdB (0 : ℝ) 0 ρ (cladeFam n) t) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (w s) :=
  expected_LA_lB_eq_of_potential h (cladeFam n) (fun t => uBlkB_nonneg t)
    (fun _ hCt => uBlkB_step_covAB h hCt)
    (fun _ hCt => tendsto_mstep_uBlkB_zero h hCt.1)
    hfw hlw hCs.1 hCs.2.1 hCs.2.2

end Rhone.Coalescent.MarginalLumping
