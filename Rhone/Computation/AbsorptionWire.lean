/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Absorption
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the absorption-time table comparison -/

@[expose] public section
namespace Rhone.Computation.AbsorptionWire
open Lean

structure Request where
  moran : Bool
  geneCopies : Nat
  initialCount : Nat
  fitness : Rat
  provenance : String
  kernel : Array (Array Rat)
  table : Array Rat
  scalar : Rat

def Request.claimed (r : Request) : Nat :=
  r.kernel.foldl (fun total row => total + row.size) 0 + r.table.size

def Request.valid (r : Request) : Bool :=
  decide (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 16 ∧ r.initialCount ≤ r.geneCopies ∧
    (r.moran = true → 0 < r.fitness) ∧ r.provenance.trimAscii.toString.isEmpty = false ∧
    r.scalar = r.table.getD r.initialCount 0)

def Request.Canonical (r : Request) : Prop := r.moran = false → r.fitness = 1

def Request.check (r : Request) : Bool :=
  if r.moran then Absorption.checkMoranReport r.geneCopies r.fitness r.kernel r.table
  else Absorption.checkWfReport r.geneCopies r.kernel r.table

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def rowEntry (entry : Json) : Except String Rat :=
  entry.getStr?.bind RationalWire.decode

def ratArray (value : Json) : Except String (Array Rat) :=
  value.getArr?.bind fun entries => entries.mapM rowEntry

def modelFields (doc : Json) (model : String) : Except String (Bool × Rat) :=
  if model == "wright-fisher" then do
    match (← doc.getObjVal? "relative_fitness") with
    | .null => pure ()
    | _ => throw "invalid WF convention"
    if (← doc.getObjValAs? String "time_unit") != "generation" then
      throw "invalid WF convention"
    return (false, 1)
  else if model == "moran" then do
    if (← doc.getObjValAs? String "time_unit") != "birth-death-event" then
      throw "invalid Moran time unit"
    let fitness ← rat doc "relative_fitness"
    return (true, fitness)
  else throw "unsupported model"

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-drift-absorption-v1" then
    throw "unsupported schema"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported semantics"
  if (← doc.getObjValAs? String "scope") !=
      "complete-supplied-discrete-zero-mutation-absorption-table" then throw "unsupported scope"
  let n ← doc.getObjValAs? Nat "gene_copies"
  let i ← doc.getObjValAs? Nat "initial_count"
  let provenance ← doc.getObjValAs? String "parameter_provenance"
  let table ← (doc.getObjVal? "mean_absorption_times").bind ratArray
  let rows ← (doc.getObjVal? "transition_kernel").bind Json.getArr?
  let kernel ← rows.mapM ratArray
  let scalar ← rat doc "mean_absorption_time"
  let model ← doc.getObjValAs? String "model"
  let fields ← modelFields doc model
  return ⟨fields.1, n, i, fields.2, provenance, kernel, table, scalar⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.claimed)
    else .error "unsupported absorption request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-absorption-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeEntry (value : Rat) : Json := .str (RationalWire.strictPrint value)

def encodeArray (values : Array Rat) : Json := .arr (values.map encodeEntry)

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-drift-absorption-v1"),
    ("comparison_semantics", toJson "exact_fraction"),
    ("scope", toJson "complete-supplied-discrete-zero-mutation-absorption-table"),
    ("model", .str (if r.moran then "moran" else "wright-fisher")),
    ("gene_copies", toJson r.geneCopies), ("initial_count", toJson r.initialCount),
    ("relative_fitness", if r.moran then encodeEntry r.fitness else .null),
    ("time_unit", .str (if r.moran then "birth-death-event" else "generation")),
    ("parameter_provenance", .str r.provenance),
    ("mean_absorption_times", encodeArray r.table),
    ("mean_absorption_time", encodeEntry r.scalar),
    ("transition_kernel", .arr (r.kernel.map encodeArray))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.AbsorptionWire
