/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericArtifact
public import Rhone.Computation.LogKernel

/-! # LDhat likelihood file bound reader with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.LdhatArtifact
open Lean GenericArtifact
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

def budget : Rat := 500001 / 1000000000

def headerBudget : Rat := 50001 / 1000000000

def parseNat (s : String) : Option Nat :=
  if !s.isEmpty && s.toList.all Char.isDigit then
    some (s.toList.foldl (fun acc ch => 10 * acc + (ch.toNat - 48)) 0)
  else none

def parseFixed (s : String) : Option Rat := do
  let (negative, body) :=
    if s.toList.head? = some '-' then (true, String.ofList (s.toList.drop 1)) else (false, s)
  match body.splitOn "." with
  | [whole, frac] =>
    let w ← parseNat whole
    let f ← parseNat frac
    let v : Rat := (w : Rat) + (f : Rat) / ((10 ^ frac.length : Nat) : Rat)
    return if negative then -v else v
  | _ => none

def tokens (line : String) : List String := (line.splitOn " ").filter (!·.isEmpty)

structure Row where
  ct : Nat
  config : Config
  values : Array Rat
  deriving Inhabited

def parseRow (line : String) : Except String Row :=
  match line.splitOn ":" with
  | [left, right] =>
    match tokens left with
    | [ct, "#", c00, c10, c01, c11] =>
      match parseNat ct, parseNat c00, parseNat c10, parseNat c01, parseNat c11 with
      | some ct, some c00, some c10, some c01, some c11 =>
        match (tokens right).mapM parseFixed with
        | some values => .ok ⟨ct, ⟨#[0, 0], #[0, 0], #[c00, c01, c10, c11]⟩, values.toArray⟩
        | none => .error "malformed LDhat value"
      | _, _, _, _, _ => .error "malformed LDhat count"
    | _ => .error "malformed LDhat data line"
  | _ => .error "malformed LDhat data line"

structure LkFile where
  n : Nat
  nConfigs : Nat
  theta : Rat
  nPts : Nat
  rhoMax : Rat
  rows : Array Row

def parseLk (text : String) : Except String LkFile :=
  match text.splitOn "\n" with
  | l1 :: l2 :: l3 :: rest =>
    match tokens l1, tokens l2, tokens l3 with
    | [n, nc], ["1", theta], [npts, rhoMax] =>
      match parseNat n, parseNat nc, parseFixed theta, parseNat npts, parseFixed rhoMax with
      | some n, some nc, some theta, some npts, some rhoMax => do
        let rows ← (rest.filter (fun line => line.contains ':')).mapM parseRow
        return ⟨n, nc, theta, npts, rhoMax, rows.toArray⟩
      | _, _, _, _, _ => .error "malformed LDhat header value"
    | _, _, _ => .error "malformed LDhat header"
  | _ => .error "missing LDhat header"

structure Request where
  artifact : GenericArtifact.Request
  lk : LkFile

def configIndex (h : Header) (x : Config) : Option Nat :=
  (List.range h.configs.size).find? fun c =>
    GenericKernel.keyOf (h.configs.getD c default) == GenericKernel.keyOf x

def rowAccepted (r : GenericArtifact.Request) (i : Nat) (row : Row) : Bool :=
  row.ct == i + 1 && row.values.size == r.header.grid.size &&
    match configIndex r.header row.config with
    | none => false
    | some c =>
      (List.range r.header.grid.size).all fun g =>
        LogKernel.bracketCheck ((r.values.getD g #[]).getD c 0) (row.values.getD g 0) budget

def Request.accepted (r : Request) : Bool :=
  let h := r.artifact.header
  r.artifact.accepted && h.thetaA == h.thetaB && h.piA == #[1 / 2, 1 / 2] &&
    h.piB == #[1 / 2, 1 / 2] && r.lk.n == h.n && r.lk.nConfigs == r.lk.rows.size &&
    r.lk.nPts == h.grid.size &&
    decide (Float64Kernel.absRat (r.lk.theta - h.thetaA / 2) ≤ headerBudget) &&
    decide (Float64Kernel.absRat (r.lk.rhoMax - h.grid.getD (h.grid.size - 1) 0) ≤
      headerBudget) &&
    (List.range r.lk.rows.size).all fun i => rowAccepted r.artifact i (r.lk.rows.getD i default)

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "table", "certificates", "text"]
  if (← doc.getObjValAs? String "op") != "check_table_ldhat_bound" then
    throw "unsupported LDhat operation"
  let table ← doc.getObjVal? "table"
  let header ← decodeHeader table
  let values ← GenericArtifact.readValues header table
  let certificates ← doc.getObjVal? "certificates" >>= readCertificates header
  let text ← doc.getObjValAs? String "text"
  let lk ← parseLk text
  return ⟨⟨header, values, certificates⟩, lk⟩

def stamp (accepted : Bool) (r : Request) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-table-ldhat-bound-check-v1"),
    ("accepted", toJson accepted), ("grid_rows", toJson r.artifact.header.grid.size),
    ("data_lines", toJson r.lk.rows.size), ("budget", toJson "500001/1000000000"),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  return stamp r.accepted r

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.LdhatArtifact
