/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.KingmanCheck
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the Kingman genealogy-moments report check -/

@[expose] public section
namespace Rhone.Computation.KingmanWire
open Lean

structure Request where
  geneCopies : Nat
  pairRate : Rat
  timeUnit : String
  meanTmrca : Rat
  varianceTmrca : Rat
  meanTotalBranchLength : Rat
  varianceTotalBranchLength : Rat

def Request.claim (r : Request) : Array Rat :=
  #[r.meanTmrca, r.varianceTmrca, r.meanTotalBranchLength, r.varianceTotalBranchLength]

def Request.valid (r : Request) : Bool :=
  decide (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ r.pairRate = 1)

def Request.ofFormula (n : Nat) (unit : String) : Request :=
  let m := Kingman.moments n
  ⟨n, 1, unit, m.meanTmrca, m.varianceTmrca, m.meanTotalBranchLength,
    m.varianceTotalBranchLength⟩

def unitOk (unit : String) : Bool :=
  !(unit.isEmpty || unit.utf8ByteSize > 64 || unit.trimAscii.toString != unit ||
    unit.toList.any (fun ch => ch.toNat < 32 || 127 ≤ ch.toNat))

def Request.Canonical (r : Request) : Prop := unitOk r.timeUnit = true

def strictRat (s : String) : Except String Rat := do
  let value ← RationalWire.decode s
  if RationalWire.strictPrint value != s then throw "noncanonical rational wire value"
  return value

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind strictRat

def checkUnit (unit : String) : Except String String :=
  if unitOk unit then .ok unit else .error "invalid supplied time-unit label"

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-genealogy-moments-v1" then
    throw "unsupported schema"
  if (← doc.getObjValAs? String "model") != "supplied_neutral_constant_size_kingman" then
    throw "unsupported model"
  if (← doc.getObjValAs? String "rate_convention") !=
      "each_unordered_pair_has_supplied_rate_per_time_unit" then
    throw "unsupported rate convention"
  let n ← doc.getObjValAs? Nat "gene_copies"
  let rate ← rat doc "pair_rate_per_unit"
  let unit ← (doc.getObjValAs? String "time_unit").bind checkUnit
  let values ← doc.getObjVal? "moments"
  let fields ← values.getObj?
  if fields.size != 4 then throw "expected exactly four moment fields"
  let meanTmrca ← rat values "mean_tmrca"
  let varianceTmrca ← rat values "variance_tmrca"
  let meanLength ← rat values "mean_total_branch_length"
  let varianceLength ← rat values "variance_total_branch_length"
  return ⟨n, rate, unit, meanTmrca, varianceTmrca, meanLength, varianceLength⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (Kingman.checkReport r.geneCopies r.claim, r.claim.size)
    else .error "unsupported sample size or pair rate"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-kingman-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false),
    ("supplied_rate_scaling_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def momentFields (r : Request) : List (String × Json) :=
  [("mean_tmrca", encodeRat r.meanTmrca), ("variance_tmrca", encodeRat r.varianceTmrca),
    ("mean_total_branch_length", encodeRat r.meanTotalBranchLength),
    ("variance_total_branch_length", encodeRat r.varianceTotalBranchLength)]

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-genealogy-moments-v1"),
    ("model", toJson "supplied_neutral_constant_size_kingman"),
    ("rate_convention", toJson "each_unordered_pair_has_supplied_rate_per_time_unit"),
    ("gene_copies", toJson r.geneCopies), ("pair_rate_per_unit", encodeRat r.pairRate),
    ("time_unit", .str r.timeUnit), ("moments", Json.mkObj (momentFields r))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.KingmanWire
