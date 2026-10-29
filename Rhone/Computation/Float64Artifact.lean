/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericArtifact
public import Rhone.Computation.Float64Kernel

/-! # Float64 table artifact reader with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.Float64Artifact
open Lean GenericArtifact Float64Kernel
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

def floatFields : List String := tableFields ++ ["float64_export"]

def numberValue (n : JsonNumber) : Rat := (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

def readLeaf (leaf : Json) : Except String (Rat × Rat) := do
  fieldsAllowed leaf ["exact", "float"]
  let exact ← strictField leaf "exact"
  let number ← leaf.getObjVal? "float" >>= Json.getNum?
  return (exact, numberValue number)

def readFloatRow (keys : Array String) (row : Json) : Except String (Array (Rat × Rat)) := do
  fieldsAllowed row keys.toList
  keys.mapM fun key => row.getObjVal? key >>= readLeaf

def readFloatValues (h : Header) (doc : Json) : Except String (Array (Array (Rat × Rat))) := do
  let values ← doc.getObjVal? "values"
  fieldsAllowed values h.gridKeys.toList
  h.gridKeys.mapM fun gridKey => values.getObjVal? gridKey >>= readFloatRow h.keys

def readExport (doc : Json) : Except String (Rat × Nat) := do
  let summary ← doc.getObjVal? "float64_export"
  fieldsAllowed summary ["max_relative_error", "n_values"]
  let maxError ← strictField summary "max_relative_error"
  let count ← summary.getObjValAs? Nat "n_values"
  return (maxError, count)

structure Request where
  header : Header
  leaves : Array (Array (Rat × Rat))
  maxError : Rat
  count : Nat
  certificates : Array (Array (Config × Rat))

def Request.artifact (r : Request) : GenericArtifact.Request :=
  ⟨r.header, r.leaves.map (·.map Prod.fst), r.certificates⟩

def exactCell (leaf : Rat × Rat) : Cell :=
  ⟨leaf.1, nearestWord leaf.1, binade leaf.1⟩

def decimalCell (leaf : Rat × Rat) : Cell :=
  ⟨leaf.2, nearestWord leaf.1, binade leaf.2⟩

def Request.allLeaves (r : Request) : List (Rat × Rat) :=
  r.leaves.toList.flatMap Array.toList

def Request.accepted (r : Request) : Bool :=
  r.artifact.accepted && cellsAccepted (r.allLeaves.map exactCell) &&
    cellsAccepted (r.allLeaves.map decimalCell) && r.count == r.allLeaves.length &&
    r.maxError == maxRelativeError (r.allLeaves.map exactCell)

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "table", "certificates"]
  if (← doc.getObjValAs? String "op") != "check_table_artifact_float64" then
    throw "unsupported float64 table operation"
  let table ← doc.getObjVal? "table"
  let header ← decodeHeaderAs "rhone-table-float64-v3" floatFields table
  let leaves ← readFloatValues header table
  let (maxError, count) ← readExport table
  let certificates ← doc.getObjVal? "certificates" >>= readCertificates header
  return ⟨header, leaves, maxError, count, certificates⟩

def stamp (accepted : Bool) (r : Request) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-table-float64-check-v1"),
    ("accepted", toJson accepted), ("grid_rows", toJson r.header.grid.size),
    ("configurations", toJson r.header.keys.size),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  return stamp r.accepted r

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.Float64Artifact
