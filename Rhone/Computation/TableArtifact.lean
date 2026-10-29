/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWire
public import Std.Data.HashMap.Basic

/-! # Exact two-allele table artifact reader with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.TableArtifact
open Lean

def fieldsAllowed (doc : Json) (allowed : List String) : Except String Unit := do
  let fields ← doc.getObj?
  if fields.toList.all (fun field => allowed.contains field.1) then return ()
  else throw "unsupported table artifact field"

def strictRational (text : String) : Except String Rat := do
  let value ← RationalWire.decode text
  if text != RationalWire.strictPrint value then throw "noncanonical table fraction"
  return value

def strictField (doc : Json) (name : String) : Except String Rat :=
  doc.getObjValAs? String name >>= strictRational

def strictArray (doc : Json) (name : String) : Except String (Array Rat) := do
  let texts ← doc.getObjValAs? (Array String) name
  texts.mapM strictRational

def baselineModel : String :=
  "mutation=pim;selection=neutral;demography=stationary;sampling=contemporaneous;" ++
  "loci=2;structure=panmictic;adapter=autosomal"

def tableFields : List String :=
  ["schema", "release_status", "rhone_version", "model", "comparison_semantics", "source",
    "description", "n0", "KA", "KB", "thetaA", "thetaB", "piA", "piB", "rho_grid", "n_configs",
    "configs", "completed_rows", "values", "provenance"]

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

def decodeHeader (doc : Json) : Except String Header := do
  fieldsAllowed doc tableFields
  if (← doc.getObjValAs? String "schema") != "rhone-table-v3" then
    throw "unsupported exact artifact schema"
  if (← doc.getObjValAs? String "model") != baselineModel then
    throw "unsupported exact table model"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported table comparison semantics"
  let thetaA ← strictField doc "thetaA"
  let thetaB ← strictField doc "thetaB"
  let piA ← strictArray doc "piA"
  let piB ← strictArray doc "piB"
  if (← doc.getObjValAs? Nat "KA") != 2 then throw "only two alleles at locus A"
  if (← doc.getObjValAs? Nat "KB") != 2 then throw "only two alleles at locus B"
  let n ← doc.getObjValAs? Nat "n0"
  let keys ← doc.getObjValAs? (Array String) "configs"
  let configs ← keys.mapM (fun key => parseConfig key)
  if (← doc.getObjValAs? Nat "n_configs") != keys.size then
    throw "table configuration count mismatch"
  let gridKeys ← doc.getObjValAs? (Array String) "rho_grid"
  let grid ← gridKeys.mapM strictRational
  if (← doc.getObjValAs? Nat "completed_rows") != grid.size then
    throw "partial table artifact"
  return ⟨thetaA, thetaB, piA, piB, n, keys, configs, gridKeys, grid⟩

def readRow (keys : Array String) (row : Json) : Except String (Array Rat) := do
  fieldsAllowed row keys.toList
  keys.mapM fun key => strictField row key

def readValues (h : Header) (doc : Json) : Except String (Array (Array Rat)) := do
  let values ← doc.getObjVal? "values"
  fieldsAllowed values h.gridKeys.toList
  h.gridKeys.mapM fun gridKey => do
    let row ← values.getObjVal? gridKey
    readRow h.keys row

def readCertificates (h : Header) (doc : Json) : Except String (Array (Array (Config × Rat))) := do
  let certificates ← doc.getArr?
  if certificates.size != h.grid.size then throw "table certificate count mismatch"
  certificates.mapM CheckerWire.entries

structure Request where
  header : Header
  values : Array (Array Rat)
  certificates : Array (Array (Config × Rat))

def lookup (certificate : Array (Config × Rat)) : Std.HashMap String Rat :=
  certificate.foldl (fun m e => m.insert e.1.key e.2) {}

def rowAccepted (h : Header) (rho : Rat) (values : Array Rat)
    (certificate : Array (Config × Rat)) : Bool :=
  values.size == h.keys.size && checkTable (h.params rho) h.n certificate &&
    let table := lookup certificate
    (List.range h.keys.size).all fun c => table.get? (h.keys.getD c "") == some (values.getD c 0)

def Request.accepted (r : Request) : Bool :=
  r.values.size == r.header.grid.size && r.certificates.size == r.header.grid.size &&
    (List.range r.header.grid.size).all fun g =>
      rowAccepted r.header (r.header.grid.getD g 0) (r.values.getD g #[])
        (r.certificates.getD g #[])

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "table", "certificates"]
  if (← doc.getObjValAs? String "op") != "check_table_artifact_exact" then
    throw "unsupported exact table operation"
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

end Rhone.Computation.TableArtifact
