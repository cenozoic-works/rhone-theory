/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Checker
public import Rhone.Computation.ParamsWireTyped
public import Lean.Data.Json

/-! # Exact finite-checker JSON AST surface -/

@[expose] public section
namespace Rhone.Computation.CheckerWire
open Lean

def entry (row : Json) : Except String (Config × Rat) := do
  let key ← row.getObjValAs? String "key"
  let value ← row.getObjValAs? String "value" >>= RationalWire.decode
  let config ← parseConfig key
  return (config, value)

def entries (value : Json) : Except String (Array (Config × Rat)) := do
  let rows ← value.getArr?
  rows.mapM entry

def entryFields (row : Config × Rat) : List (String × Json) :=
  [("key", .str row.1.key), ("value", .str (RationalWire.strictPrint row.2))]

def encodeEntry (row : Config × Rat) : Json := Json.mkObj (entryFields row)

def stamp (fields : List (String × Json)) : Json :=
  Json.mkObj ([("schema", toJson "rhone-compute-checker-v1"),
    ("verification", toJson "phase0-unverified"),
    ("soundness_proved", toJson false), ("completeness_proved", toJson false)] ++ fields)

def requestAst (doc : Json) : Except String Json := do
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table" then throw "unsupported operation"
  let bound ← doc.getObjValAs? Nat "n"
  if bound > 65535 then throw "unsupported bound: exceeds the u16 configuration wire domain"
  let params ← ParamsWire.decodeTyped doc
  if !params.valid then throw "invalid parameter domain"
  let rows ← doc.getObjVal? "entries" >>= entries
  return stamp [("accepted", toJson (checkTable params bound rows)),
    ("bound", toJson bound), ("row_count", toJson rows.size)]

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def response (value : Except String Json) : Json :=
  match value with
  | .ok result => result
  | .error error => stamp [("accepted", toJson false), ("error", toJson error)]

def requestFields (p : Params) (n : Nat) (rows : Array (Config × Rat)) :
    List (String × Json) :=
  [("op", toJson "check_table"), ("n", toJson n)] ++
    ParamsWire.fields p ++ [("entries", .arr (rows.map encodeEntry))]

def encodeRequest (p : Params) (n : Nat) (rows : Array (Config × Rat)) : Json :=
  Json.mkObj (requestFields p n rows)

end Rhone.Computation.CheckerWire
