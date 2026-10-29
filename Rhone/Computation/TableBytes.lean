/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericArtifact

/-! # Exact table artifact bytes with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.TableBytes
open Lean GenericArtifact
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

def releaseStatus : String :=
  "{\"schema\":\"rhone-release-status-v1\",\"status\":\"unchecked\"," ++
  "\"verification\":\"phase0-unverified\",\"json_boundary_equality_proved\":false," ++
  "\"rust_implementation_equality_proved\":false}"

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c.val = 8 then "\\b"
  else if c.val = 12 then "\\f"
  else if c = '\n' then "\\n"
  else if c = '\r' then "\\r"
  else if c = '\t' then "\\t"
  else if c.val < 32 then
    String.ofList ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else String.singleton c

def jsonString (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

def compact : Nat → Json → Option String
  | 0, _ => none
  | _ + 1, .null => some "null"
  | _ + 1, .bool true => some "true"
  | _ + 1, .bool false => some "false"
  | _ + 1, .num n => if n.exponent = 0 then some (toString n.mantissa) else none
  | _ + 1, .str s => some (jsonString s)
  | fuel + 1, .arr xs => do
    let parts ← xs.toList.mapM (compact fuel)
    return "[" ++ String.intercalate "," parts ++ "]"
  | fuel + 1, .obj kvs => do
    let parts ← (kvs.toList.mapM fun (k, v) => do
      let body ← compact fuel v
      return jsonString k ++ ":" ++ body)
    return "{" ++ String.intercalate "," parts ++ "}"

def provenanceDepth : Nat := 64

def fieldRaw (name raw : String) : String := "  " ++ jsonString name ++ ": " ++ raw ++ ",\n"

def fieldStr (name value : String) : String := fieldRaw name (jsonString value)

def fieldArray (name : String) (items : List String) : String :=
  if items.isEmpty then fieldRaw name "[]"
  else "  " ++ jsonString name ++ ": [\n" ++
    String.intercalate ",\n" (items.map fun item => "    " ++ jsonString item) ++ "\n  ],\n"

def valueRow (keys : List String) (gridKey : String) (row : List Rat) (last : Bool) : String :=
  let lines := (keys.zip row).map fun (key, value) =>
    "      " ++ jsonString key ++ ": " ++ jsonString (RationalWire.strictPrint value)
  "    " ++ jsonString gridKey ++ ": {
" ++
    (if lines.isEmpty then "" else String.intercalate ",
" lines ++ "
") ++
    (if last then "    }
" else "    },
")

def valuesBlock (keys : List String) (rows : List (String × List Rat)) : String :=
  if rows.isEmpty then "  \"values\": {},
"
  else
    let n := rows.length
    "  \"values\": {
" ++
      String.join (rows.zipIdx.map fun ((gridKey, row), k) =>
        valueRow keys gridKey row (k + 1 == n)) ++ "  },
"

structure Meta where
  version : String
  source : String
  description : Option String
  provenance : Json

def decodeMeta (doc : Json) : Except String Meta := do
  let version ← doc.getObjValAs? String "rhone_version"
  let source ← doc.getObjValAs? String "source"
  let description ← match doc.getObjVal? "description" with
    | .ok value => some <$> value.getStr?
    | .error _ => pure none
  let provenance ← doc.getObjVal? "provenance"
  return ⟨version, source, description, provenance⟩

def render (h : Header) (values : Array (Array Rat)) (m : Meta) : Option String := do
  let provenance ← compact provenanceDepth m.provenance
  let frac := RationalWire.strictPrint
  let keys := h.configs.toList.map Config.key
  let gridKeys := h.grid.toList.map frac
  return "{
" ++ fieldStr "schema" "rhone-table-v3" ++ fieldRaw "release_status" releaseStatus ++
    fieldStr "rhone_version" m.version ++ fieldStr "model" baselineModel ++
    fieldStr "comparison_semantics" "exact_fraction" ++ fieldStr "source" m.source ++
    (match m.description with | some d => fieldStr "description" d | none => "") ++
    fieldRaw "n0" (toString h.n) ++ fieldRaw "KA" (toString h.piA.size) ++
    fieldRaw "KB" (toString h.piB.size) ++ fieldStr "thetaA" (frac h.thetaA) ++
    fieldStr "thetaB" (frac h.thetaB) ++ fieldArray "piA" (h.piA.toList.map frac) ++
    fieldArray "piB" (h.piB.toList.map frac) ++ fieldArray "rho_grid" gridKeys ++
    fieldRaw "n_configs" (toString h.configs.size) ++ fieldArray "configs" keys ++
    fieldRaw "completed_rows" (toString h.grid.size) ++
    valuesBlock keys (gridKeys.zip (values.toList.map Array.toList)) ++
    "  \"provenance\": " ++ provenance ++ "
}
"

structure Request where
  text : String
  header : Header
  values : Array (Array Rat)
  info : Meta
  certificates : Array (Array (Config × Rat))

def Request.artifact (r : Request) : GenericArtifact.Request :=
  ⟨r.header, r.values, r.certificates⟩

def Request.accepted (r : Request) : Bool :=
  r.artifact.accepted && render r.header r.values r.info == some r.text

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "text", "certificates"]
  if (← doc.getObjValAs? String "op") != "check_table_artifact_bytes" then
    throw "unsupported table bytes operation"
  let text ← doc.getObjValAs? String "text"
  let table ← Json.parse text
  let header ← decodeHeader table
  let values ← readValues header table
  let info ← decodeMeta table
  let certificates ← doc.getObjVal? "certificates" >>= readCertificates header
  return ⟨text, header, values, info, certificates⟩

def stamp (accepted : Bool) (r : Request) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-table-bytes-check-v1"),
    ("accepted", toJson accepted), ("grid_rows", toJson r.header.grid.size),
    ("configurations", toJson r.header.keys.size), ("bytes", toJson r.text.utf8ByteSize),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  return stamp r.accepted r

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.TableBytes
