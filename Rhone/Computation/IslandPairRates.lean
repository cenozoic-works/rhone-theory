/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.IslandPairWire

/-! # Island-pair report with its four rate fields -/

@[expose] public section
namespace Rhone.Computation.IslandPairRates
open Lean IslandPairWire

def destinationRate (d : Nat) (m : Rat) : Rat := m / (d - 1 : Nat)

def rateValues (d : Nat) (m c : Rat) : Array Rat :=
  #[destinationRate d m, c, 2 * m, 2 * destinationRate d m]

def checkRates (d : Nat) (m c : Rat) (claim : Array Rat) : Bool :=
  decide (claim = rateValues d m c)

structure Request where
  report : Report
  destination : Rat
  sameToCoalesced : Rat
  sameToDifferent : Rat
  differentToSame : Rat

def Request.rates (r : Request) : Array Rat :=
  #[r.destination, r.sameToCoalesced, r.sameToDifferent, r.differentToSame]

def Request.check (r : Request) : Bool :=
  IslandPair.check r.report.demes r.report.migration r.report.coalescence r.report.claim &&
    checkRates r.report.demes r.report.migration r.report.coalescence r.rates

def Request.count (r : Request) : Nat := r.report.claim.size + r.rates.size

def Request.ofFormula (d : Nat) (m c : Rat) (timeUnit provenance : String) : Request :=
  ⟨Report.ofFormula d m c timeUnit provenance, destinationRate d m, c, 2 * m,
    2 * destinationRate d m⟩

def decode (doc : Json) : Except String Request := do
  let report ← IslandPairWire.decode doc
  let destination ← rat doc "per_destination_lineage_migration_rate"
  let sameToCoalesced ← rat doc "same_to_coalesced_rate"
  let sameToDifferent ← rat doc "same_to_different_rate"
  let differentToSame ← rat doc "different_to_same_rate"
  return ⟨report, destination, sameToCoalesced, sameToDifferent, differentToSame⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.report.valid then .ok (r.check, r.count)
    else .error "unsupported island-pair request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-island-pair-rates-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def requestFields (r : Request) : List (String × Json) :=
  IslandPairWire.requestFields r.report ++
    [("per_destination_lineage_migration_rate", encodeRat r.destination),
      ("same_to_coalesced_rate", encodeRat r.sameToCoalesced),
      ("same_to_different_rate", encodeRat r.sameToDifferent),
      ("different_to_same_rate", encodeRat r.differentToSame)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.IslandPairRates
