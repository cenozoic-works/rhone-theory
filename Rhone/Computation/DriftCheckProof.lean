/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.DriftCheck

/-! # Soundness and completeness of the Wright-Fisher and Moran drift report checks -/

@[expose] public section
namespace Rhone.Computation.Drift

theorem checkWfReport_iff (n i t : Nat) (claim : Array Rat) :
    checkWfReport n i t claim = true ↔ claim = wfReportValues n i t := by
  simp [checkWfReport]

theorem checkWfReport_complete (n i t : Nat) :
    checkWfReport n i t (wfReportValues n i t) = true := by simp [checkWfReport]

theorem checkMoranReport_iff (n : Nat) (r : Rat) (i t : Nat) (claim : Array Rat) :
    checkMoranReport n r i t claim = true ↔ claim = moranReportValues n r i t := by
  simp [checkMoranReport]

theorem checkMoranReport_complete (n : Nat) (r : Rat) (i t : Nat) :
    checkMoranReport n r i t (moranReportValues n r i t) = true := by
  simp [checkMoranReport]

end Rhone.Computation.Drift
