/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Kingman
public import Rhone.Computation.SfsProof
public import Rhone.Coalescent.Kingman

/-! # Canonical executable values equal the unchanged rational specifications -/

@[expose] public section
namespace Rhone.Computation.Kingman
open Finset

theorem varianceTime_eq (n : Nat) :
    varianceTime n = ∑ k ∈ Icc 2 n, holding k ^ 2 := by
  induction n with
  | zero => simp [varianceTime]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [varianceTime, holding]
    · rw [varianceTime, ih, Finset.sum_Icc_succ_top (by omega)]

theorem meanTmrca_eq (n : Nat) :
    (moments n).meanTmrca = Rhone.Coalescent.expTMRCA n := by
  by_cases hn : n = 0
  · subst n
    simp [moments, Rhone.Coalescent.expTMRCA]
  · rw [Rhone.Coalescent.expTMRCA_eq (by omega)]
    simp [moments, hn]

theorem varianceTmrca_eq (n : Nat) :
    (moments n).varianceTmrca = Rhone.Coalescent.varTMRCA n := by
  change varianceTime n = _
  rw [varianceTime_eq, Rhone.Coalescent.varTMRCA_eq]
  rfl

theorem meanTotalBranchLength_eq (n : Nat) :
    (moments n).meanTotalBranchLength = Rhone.Coalescent.expLength n := by
  change 2 * (Sfs.coefficients n).a1 = _
  rw [Rhone.Coalescent.expLength_eq]
  simp [Sfs.coefficients, Sfs.harmonic_eq]

theorem varianceTotalBranchLength_eq (n : Nat) :
    (moments n).varianceTotalBranchLength = Rhone.Coalescent.varLength n := by
  change 4 * (Sfs.coefficients n).a2 = _
  rw [Rhone.Coalescent.varLength_eq]
  simp [Sfs.coefficients, Sfs.harmonic2_eq]

end Rhone.Computation.Kingman
