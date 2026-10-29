/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.TableArtifact
public import Rhone.Computation.GenericKernel

/-! # Exact general-allele table artifact reader with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.GenericArtifact
open Lean TableArtifact

structure Header where
  thetaA : Rat
  thetaB : Rat
  piA : Array Rat
  piB : Array Rat
  n : Nat
  keys : Array String
  configs : Array Config
  gridKeys : Array String
  grid : Array Rat

def Header.params (h : Header) (rho : Rat) : Params := ⟨h.thetaA, h.thetaB, rho, h.piA, h.piB⟩

def require (test : Bool) (message : String) : Except String Unit :=
  if test then pure () else throw message

def decodeHeaderAs (schema : String) (allowed : List String) (doc : Json) :
    Except String Header := do
  fieldsAllowed doc allowed
  require ((← doc.getObjValAs? String "schema") == schema) "unsupported exact artifact schema"
  require ((← doc.getObjValAs? String "model") == baselineModel) "unsupported exact table model"
  require ((← doc.getObjValAs? String "comparison_semantics") == "exact_fraction")
    "unsupported table comparison semantics"
  let thetaA ← strictField doc "thetaA"
  let thetaB ← strictField doc "thetaB"
  let piA ← strictArray doc "piA"
  let piB ← strictArray doc "piB"
  let ka ← doc.getObjValAs? Nat "KA"
  let kb ← doc.getObjValAs? Nat "KB"
  require (piA.size == ka) "allele count mismatch at locus A"
  require (piB.size == kb) "allele count mismatch at locus B"
  let n ← doc.getObjValAs? Nat "n0"
  let keys ← doc.getObjValAs? (Array String) "configs"
  let configs ← keys.mapM (fun key => parseConfig key ka kb)
  require ((← doc.getObjValAs? Nat "n_configs") == keys.size)
    "table configuration count mismatch"
  let gridKeys ← doc.getObjValAs? (Array String) "rho_grid"
  let grid ← gridKeys.mapM strictRational
  require ((← doc.getObjValAs? Nat "completed_rows") == grid.size) "partial table artifact"
  return ⟨thetaA, thetaB, piA, piB, n, keys, configs, gridKeys, grid⟩

def decodeHeader (doc : Json) : Except String Header :=
  decodeHeaderAs "rhone-table-v3" tableFields doc

def readValues (h : Header) (doc : Json) : Except String (Array (Array Rat)) := do
  let values ← doc.getObjVal? "values"
  fieldsAllowed values h.gridKeys.toList
  h.gridKeys.mapM fun gridKey => do
    let row ← values.getObjVal? gridKey
    readRow h.keys row

def readCertificate (h : Header) (doc : Json) : Except String (Array (Config × Rat)) := do
  let rows ← doc.getArr?
  rows.mapM (GenericKernel.entry h.piA.size h.piB.size)

def readCertificates (h : Header) (doc : Json) :
    Except String (Array (Array (Config × Rat))) := do
  let certificates ← doc.getArr?
  if certificates.size != h.grid.size then throw "table certificate count mismatch"
  certificates.mapM (readCertificate h)

structure Request where
  header : Header
  values : Array (Array Rat)
  certificates : Array (Array (Config × Rat))

def Header.check (h : Header) (rho : Rat) (certificate : Array (Config × Rat)) :
    GenericKernel.Request :=
  ⟨h.params rho, h.n, certificate⟩

def valuesMatch (h : Header) (values : Array Rat) (certificate : Array (Config × Rat)) : Bool :=
  match GenericKernel.insertRows certificate.toList {} with
  | none => false
  | some table =>
    (List.range h.configs.size).all fun c =>
      table.get? (GenericKernel.keyOf (h.configs.getD c default)) == some (values.getD c 0)

def rowAccepted (h : Header) (rho : Rat) (values : Array Rat)
    (certificate : Array (Config × Rat)) : Bool :=
  values.size == h.keys.size && (h.check rho certificate).accepted &&
    valuesMatch h values certificate

def Request.accepted (r : Request) : Bool :=
  r.values.size == r.header.grid.size && r.certificates.size == r.header.grid.size &&
    (List.range r.header.grid.size).all fun g =>
      rowAccepted r.header (r.header.grid.getD g 0) (r.values.getD g #[])
        (r.certificates.getD g #[])

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "table", "certificates"]
  if (← doc.getObjValAs? String "op") != "check_table_artifact_general" then
    throw "unsupported general table operation"
  let table ← doc.getObjVal? "table"
  let header ← decodeHeader table
  let values ← readValues header table
  let certificates ← doc.getObjVal? "certificates" >>= readCertificates header
  return ⟨header, values, certificates⟩

def stamp (accepted : Bool) (r : Request) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-table-artifact-check-v1"),
    ("accepted", toJson accepted), ("grid_rows", toJson r.header.grid.size),
    ("configurations", toJson r.header.keys.size),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  return stamp r.accepted r

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.GenericArtifact
