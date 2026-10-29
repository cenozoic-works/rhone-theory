/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.KingmanWire

/-! # Genealogy-moments report at a supplied pair rate -/

@[expose] public section
namespace Rhone.Computation.KingmanRate
open Lean KingmanWire

def scaledMoments (n : Nat) (c : Rat) : Kingman.Moments :=
  let m := Kingman.moments n
  ⟨m.meanTmrca / c, m.varianceTmrca / c ^ 2, m.meanTotalBranchLength / c,
    m.varianceTotalBranchLength / c ^ 2⟩

def reportValues (n : Nat) (c : Rat) : Array Rat :=
  let m := scaledMoments n c
  #[m.meanTmrca, m.varianceTmrca, m.meanTotalBranchLength, m.varianceTotalBranchLength]

def checkReport (n : Nat) (c : Rat) (claim : Array Rat) : Bool :=
  decide (claim = reportValues n c)

def valid (r : Request) : Bool :=
  decide (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 < r.pairRate)

def ofFormula (n : Nat) (c : Rat) (unit : String) : Request :=
  let m := scaledMoments n c
  ⟨n, c, unit, m.meanTmrca, m.varianceTmrca, m.meanTotalBranchLength,
    m.varianceTotalBranchLength⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if valid r then .ok (checkReport r.geneCopies r.pairRate r.claim, r.claim.size)
    else .error "unsupported sample size or pair rate"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-kingman-rate-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false),
    ("supplied_rate_scaling_proved", toJson true)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

end Rhone.Computation.KingmanRate
