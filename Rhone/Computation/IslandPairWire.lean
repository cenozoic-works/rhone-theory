/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.IslandPair
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the island-pair report comparison -/

@[expose] public section
namespace Rhone.Computation.IslandPairWire
open Lean

structure Report where
  demes : Nat
  migration : Rat
  coalescence : Rat
  timeUnit : String
  provenance : String
  same : Rat
  different : Rat
  contrast : Rat

def Report.claim (r : Report) : Array Rat := #[r.same, r.different, r.contrast]

def Report.valid (r : Report) : Bool :=
  decide (2 ≤ r.demes ∧ r.demes ≤ 65535 ∧ 0 < r.migration ∧ 0 < r.coalescence ∧
    r.timeUnit ≠ "" ∧ r.provenance ≠ "")

def Report.ofFormula (d : Nat) (m c : Rat) (timeUnit provenance : String) : Report :=
  ⟨d, m, c, timeUnit, provenance, IslandPair.sameTime d c, IslandPair.differentTime d m c,
    IslandPair.timeContrast d m c⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def decode (doc : Json) : Except String Report := do
  if (← doc.getObjValAs? String "schema") != "rhone.island_pair.v1" then
    throw "unsupported schema"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported comparison semantics"
  if (← doc.getObjValAs? String "model") !=
      "labelled symmetric finite-deme two-lineage coalescent" then throw "unsupported model"
  let d ← doc.getObjValAs? Nat "demes"
  let m ← rat doc "migration_rate"
  let c ← rat doc "coalescence_rate"
  let timeUnit ← doc.getObjValAs? String "time_unit"
  let provenance ← doc.getObjValAs? String "parameter_provenance"
  let same ← rat doc "same_deme_mean_time"
  let different ← rat doc "different_deme_mean_time"
  let contrast ← rat doc "time_contrast"
  return ⟨d, m, c, timeUnit, provenance, same, different, contrast⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (IslandPair.check r.demes r.migration r.coalescence r.claim, r.claim.size)
    else .error "unsupported island-pair request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-island-pair-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def requestFields (r : Report) : List (String × Json) :=
  [("schema", toJson "rhone.island_pair.v1"), ("comparison_semantics", toJson "exact_fraction"),
    ("model", toJson "labelled symmetric finite-deme two-lineage coalescent"),
    ("demes", toJson r.demes), ("migration_rate", encodeRat r.migration),
    ("coalescence_rate", encodeRat r.coalescence), ("time_unit", .str r.timeUnit),
    ("parameter_provenance", .str r.provenance), ("same_deme_mean_time", encodeRat r.same),
    ("different_deme_mean_time", encodeRat r.different),
    ("time_contrast", encodeRat r.contrast)]

def encode (r : Report) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.IslandPairWire
