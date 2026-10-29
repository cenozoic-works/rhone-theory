/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWire

/-! # Checked-table requests answered by response lines from proved code -/

@[expose] public section
namespace Rhone.Computation.CheckedTable
open Lean

structure Request where
  params : Params
  bound : Nat
  rows : Array (Config × Rat)

structure RowsRequest where
  params : Params
  rows : Array (Config × Rat)

inductive Response (ρ : Type) where
  | accept (request : ρ)
  | reject (request : ρ)
  | refuse (reason : String)

def Response.word {ρ : Type} : Response ρ → String
  | .accept _ => "ACCEPT"
  | .reject _ => "REJECT"
  | .refuse _ => "REFUSE"

def respond {ρ : Type} (check : ρ → Bool) : Except String ρ → Response ρ
  | .error reason => .refuse reason
  | .ok request => if check request then .accept request else .reject request

def decode (doc : Json) : Except String Request := do
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table" then throw "unsupported operation"
  let bound ← doc.getObjValAs? Nat "n"
  if bound > 65535 then throw "unsupported bound: exceeds the u16 configuration wire domain"
  let params ← ParamsWire.decodeTyped doc
  if !params.valid then throw "invalid parameter domain"
  let rows ← doc.getObjVal? "entries" >>= CheckerWire.entries
  return ⟨params, bound, rows⟩

def serveAst (doc : Json) : Response Request :=
  respond (fun request => checkTable request.params request.bound request.rows) (decode doc)

def decodeRows (doc : Json) : Except String RowsRequest := do
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_q_rows" then throw "unsupported operation"
  let params ← ParamsWire.decodeTyped doc
  if !params.valid then throw "invalid parameter domain"
  let rows ← doc.getObjVal? "entries" >>= CheckerWire.entries
  return ⟨params, rows⟩

def checkRows (p : Params) (rows : Array (Config × Rat)) : Bool :=
  p.valid && rows.all fun entry =>
    entry.1.a.size == 2 && entry.1.b.size == 2 && entry.1.c.size == 4 &&
      (match q p entry.1 with
        | .ok value => value == entry.2
        | .error _ => false)

def recomputeAst (doc : Json) : Response RowsRequest :=
  respond (fun request => checkRows request.params request.rows) (decodeRows doc)

def schema : String := "rhone-check-v1"

def protocol : Nat := 1

def requestId (doc : Json) : Json :=
  match doc.getObjValAs? String "id" with
  | .ok text => .str text
  | .error _ => .null

def envelope (pin : String) (id : Json) (operation route checker status : String)
    (fields : List (String × Json)) : Json :=
  Json.mkObj ([("schema", toJson schema), ("status", toJson status),
    ("op", toJson operation), ("route", toJson route), ("checker", toJson checker),
    ("id", id), ("theory_commit", toJson pin), ("protocol", toJson protocol)] ++ fields)

def closureDetail (pin : String) (id : Json) : Response Request → Json
  | .accept request =>
    envelope pin id "check_table" "closure" "Rhone.Computation.checkTable" "lean-checked"
      [("theorem", toJson "Rhone.Computation.CheckedTable.serve_accept_sound"),
        ("bound", toJson request.bound), ("row_count", toJson request.rows.size),
        ("params", ParamsWire.encode request.params)]
  | .reject request =>
    envelope pin id "check_table" "closure" "Rhone.Computation.checkTable" "rejected"
      [("bound", toJson request.bound), ("row_count", toJson request.rows.size),
        ("params", ParamsWire.encode request.params)]
  | .refuse reason =>
    envelope pin id "check_table" "closure" "Rhone.Computation.checkTable" "refused"
      [("error", toJson reason)]

def recomputeDetail (pin : String) (id : Json) : Response RowsRequest → Json
  | .accept request =>
    envelope pin id "check_q_rows" "recompute" "Rhone.Computation.q" "lean-checked"
      [("theorem", toJson "Rhone.Computation.CheckedTable.serveRecompute_accept_sound"),
        ("row_count", toJson request.rows.size),
        ("params", ParamsWire.encode request.params)]
  | .reject request =>
    envelope pin id "check_q_rows" "recompute" "Rhone.Computation.q" "rejected"
      [("row_count", toJson request.rows.size),
        ("params", ParamsWire.encode request.params)]
  | .refuse reason =>
    envelope pin id "check_q_rows" "recompute" "Rhone.Computation.q" "refused"
      [("error", toJson reason)]

def render {ρ : Type} (outcome : Response ρ) (detail : Json) : String :=
  outcome.word ++ " " ++ detail.compress

def serveWith {ρ : Type} (handler : Json → Response ρ) (detail : Json → Response ρ → Json)
    (line : String) : String :=
  match Json.parse line with
  | .error reason => render (.refuse reason : Response ρ) (detail .null (.refuse reason))
  | .ok doc => render (handler doc) (detail (requestId doc) (handler doc))

def serve (pin line : String) : String :=
  serveWith serveAst (closureDetail pin) line

def serveRecompute (pin line : String) : String :=
  serveWith recomputeAst (recomputeDetail pin) line

end Rhone.Computation.CheckedTable
