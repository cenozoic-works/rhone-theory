/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PartialSelfing
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the partial-selfing generation-law report -/

@[expose] public section
namespace Rhone.Computation.PartialSelfingWire
open Lean

structure Request where
  labels : Array String
  generations : Nat
  provenance : String
  selfing : Rat
  initial : Array Rat
  outcross : Array Rat
  table : Array (Array Rat)
  moments : Array Rat
  equilibrium : Rat
  kinship : Rat

def Request.dimension (r : Request) : Nat := r.labels.size

def Request.environment (r : Request) : Array Rat :=
  PartialSelfing.lawArray r.dimension
    (PartialSelfing.outcross (PartialSelfing.parentLaw r.dimension r.outcross))

def Request.valid (r : Request) : Bool :=
  decide (2 ≤ r.labels.size ∧ r.labels.size ≤ 8 ∧
    r.labels.toList.eraseDups.length = r.labels.size ∧ r.generations ≤ 128 ∧
    r.provenance.trimAscii.toString.isEmpty = false ∧
    PartialSelfing.ValidInput r.dimension r.generations r.selfing r.outcross r.initial)

def Request.check (r : Request) : Bool :=
  PartialSelfing.check r.dimension r.generations r.selfing r.outcross r.initial r.environment
    r.table r.moments r.equilibrium r.kinship

def Request.count (r : Request) : Nat :=
  (r.generations + 1) * (r.dimension * r.dimension + 1) + 2

def ratEntry (entry : Json) : Except String Rat :=
  entry.getStr?.bind RationalWire.decode

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def ratArray (doc : Json) : Except String (Array Rat) :=
  doc.getArr?.bind (·.mapM ratEntry)

def ratTable (doc : Json) : Except String (Array (Array Rat)) :=
  doc.getArr?.bind (·.mapM ratArray)

def labelArray (doc : Json) : Except String (Array String) :=
  doc.getArr?.bind (·.mapM Json.getStr?)

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-partial-selfing-v1" then
    throw "unsupported report schema"
  if (← doc.getObjValAs? String "model") != "partial-selfing-unrelated-outcross-environment"
  then throw "unsupported genetic model"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported comparison semantics"
  if (← doc.getObjValAs? String "time_unit") != "discrete-generation" then
    throw "unsupported time unit"
  if (← doc.getObjValAs? String "founder_identity") != "explicit-copy-label-equality-IBD"
  then throw "unsupported founder identity"
  if (← doc.getObjValAs? String "outcross_environment") !=
      "constant-supplied-joint-law-current-marginals-not-assumed" then
    throw "unsupported outcross environment"
  if (← doc.getObjValAs? String "law_coordinate_order") != "a*d+b" then
    throw "unsupported diploid ordering"
  if (← doc.getObjValAs? String "outcross_coordinate_order") != "((a*d+b)*d+c)*d+e" then
    throw "unsupported joint-parent ordering"
  let input ← doc.getObjVal? "request"
  if (← input.getObjValAs? String "schema") != "rhone-partial-selfing-request-v1" then
    throw "unsupported input schema"
  let labels ← (input.getObjVal? "founder_labels").bind labelArray
  let generations ← input.getObjValAs? Nat "generations"
  let provenance ← input.getObjValAs? String "parameter_provenance"
  let selfing ← rat input "selfing_fraction"
  let initial ← (input.getObjVal? "initial_diploid_law").bind ratArray
  let outcross ← (input.getObjVal? "outcross_parent_pair_law").bind ratArray
  let table ← (doc.getObjVal? "generation_laws").bind ratTable
  let moments ← (doc.getObjVal? "inbreeding").bind ratArray
  let equilibrium ← rat doc "equilibrium_inbreeding"
  let kinship ← rat doc "outcross_kinship"
  return ⟨labels, generations, provenance, selfing, initial, outcross, table, moments,
    equilibrium, kinship⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.count)
    else .error "invalid complete supplied genetic laws"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-partial-selfing-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeEntry (value : Rat) : Json := .str (RationalWire.strictPrint value)

def encodeArray (values : Array Rat) : Json := .arr (values.map encodeEntry)

def inputFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-partial-selfing-request-v1"),
    ("founder_labels", .arr (r.labels.map Json.str)),
    ("selfing_fraction", encodeEntry r.selfing),
    ("initial_diploid_law", encodeArray r.initial),
    ("outcross_parent_pair_law", encodeArray r.outcross),
    ("generations", toJson r.generations),
    ("parameter_provenance", .str r.provenance)]

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-partial-selfing-v1"),
    ("model", toJson "partial-selfing-unrelated-outcross-environment"),
    ("comparison_semantics", toJson "exact_fraction"),
    ("time_unit", toJson "discrete-generation"),
    ("founder_identity", toJson "explicit-copy-label-equality-IBD"),
    ("law_coordinate_order", toJson "a*d+b"),
    ("outcross_coordinate_order", toJson "((a*d+b)*d+c)*d+e"),
    ("outcross_environment", toJson "constant-supplied-joint-law-current-marginals-not-assumed"),
    ("request", Json.mkObj (inputFields r)),
    ("generation_laws", .arr (r.table.map encodeArray)),
    ("inbreeding", encodeArray r.moments),
    ("equilibrium_inbreeding", encodeEntry r.equilibrium),
    ("outcross_kinship", encodeEntry r.kinship)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.PartialSelfingWire
