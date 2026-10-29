/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.KingmanProof
public import Rhone.Coalescent.KingmanVariances

/-! # Canonical executable moments of the jump-and-hold Kingman law -/

@[expose] public section
namespace Rhone.Computation.Kingman
open MeasureTheory Coalescent Rhone.Combinatorics MarkovChain Statistics

theorem lintegral_tmrca_eq_compute (n : Nat) :
    (∫⁻ p, tmrca n p ∂(blockChain n).jumpHoldLaw (Fin.last n)) =
      ENNReal.ofReal ((moments n).meanTmrca : Real) := by
  rw [meanTmrca_eq]
  exact lintegral_tmrca n

theorem lintegral_treeLength_eq_compute (n : Nat) :
    (∫⁻ p, treeLength n p ∂(blockChain n).jumpHoldLaw (Fin.last n)) =
      ENNReal.ofReal ((moments n).meanTotalBranchLength : Real) := by
  rw [meanTotalBranchLength_eq]
  exact lintegral_treeLength n

theorem variance_tmrca_eq_compute (n : Nat) :
    ProbabilityTheory.variance (fun p => (tmrca n p).toReal)
      ((blockChain n).jumpHoldLaw (Fin.last n)) =
        ((moments n).varianceTmrca : Real) := by
  rw [varianceTmrca_eq]
  exact variance_tmrca n

theorem variance_treeLength_eq_compute (n : Nat) :
    ProbabilityTheory.variance (fun p => (treeLength n p).toReal)
      ((blockChain n).jumpHoldLaw (Fin.last n)) =
        ((moments n).varianceTotalBranchLength : Real) := by
  rw [varianceTotalBranchLength_eq]
  exact variance_treeLength n

end Rhone.Computation.Kingman
