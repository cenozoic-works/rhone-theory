/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Float64Artifact

/-! # Binary64 check of reported q values with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.QFloat
open Lean Float64Kernel
open TableArtifact (fieldsAllowed)

structure Request where
  leaves : Array (Rat × Rat)

def Request.accepted (r : Request) : Bool :=
  cellsAccepted (r.leaves.toList.map Float64Artifact.exactCell) &&
    cellsAccepted (r.leaves.toList.map Float64Artifact.decimalCell)

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "values"]
  if (← doc.getObjValAs? String "op") != "check_q_float" then
    throw "unsupported q float operation"
  let values ← doc.getObjVal? "values" >>= Json.getArr?
  let leaves ← values.mapM Float64Artifact.readLeaf
  return ⟨leaves⟩

def stamp (accepted : Bool) (r : Request) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-q-float-check-v1"),
    ("accepted", toJson accepted), ("values", toJson r.leaves.size),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  return stamp r.accepted r

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.QFloat
