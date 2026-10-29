/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Drift

/-! # Exact comparison of ordered transition entries, fixation, and neutral decay -/

@[expose] public section
namespace Rhone.Computation.Drift

def wfReportValues (n i t : Nat) : Array Rat :=
  wfTransition n i ++ #[neutralFixation n i, wfHeterozygosity n i t]

def moranReportValues (n : Nat) (r : Rat) (i t : Nat) : Array Rat :=
  moranTransition n r i ++ #[moranFixation n r i] ++
    (if r = 1 then #[moranHeterozygosity n i t] else #[])

def checkWfReport (n i t : Nat) (claim : Array Rat) : Bool :=
  decide (claim = wfReportValues n i t)

def checkMoranReport (n : Nat) (r : Rat) (i t : Nat) (claim : Array Rat) : Bool :=
  decide (claim = moranReportValues n r i t)

end Rhone.Computation.Drift
