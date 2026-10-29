/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.EffectiveSize
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the effective-size comparison -/

@[expose] public section
namespace Rhone.Computation.EffectiveSizeWire
open Lean

inductive Query where
  | harmonic (sizes : List Rat)
  | unequalSex (males females : Nat)
  | variance (p v : Rat)
  | offspring (copies : Nat) (sigma2 : Rat)

def Query.value : Query → Option Rat
  | .harmonic sizes => EffectiveSize.harmonicMean sizes
  | .unequalSex males females => EffectiveSize.unequalSexEffective males females
  | .variance p v => EffectiveSize.varianceEffective p v
  | .offspring copies sigma2 => EffectiveSize.offspringVarianceEffective copies sigma2

def Query.name : Query → String
  | .harmonic _ => "harmonic_mean"
  | .unequalSex _ _ => "unequal_sex"
  | .variance _ _ => "variance"
  | .offspring _ _ => "offspring_variance"

def Query.entries : Query → Nat
  | .harmonic sizes => sizes.length
  | _ => 0

structure Request where
  query : Query
  claim : Rat

def Request.valid (r : Request) : Bool :=
  r.query.value.isSome && decide (r.query.entries ≤ 4096)

def Request.check (r : Request) : Bool := decide (r.query.value = some r.claim)

def Request.ofFormula (query : Query) : Request := ⟨query, query.value.getD 0⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def rowEntry (entry : Json) : Except String Rat :=
  entry.getStr?.bind RationalWire.decode

def ratArray (value : Json) : Except String (Array Rat) :=
  value.getArr?.bind fun entries => entries.mapM rowEntry

def query (doc : Json) (quantity : String) : Except String Query :=
  if quantity == "harmonic_mean" then do
    let sizes ← (doc.getObjVal? "sizes").bind ratArray
    return .harmonic sizes.toList
  else if quantity == "unequal_sex" then do
    let males ← doc.getObjValAs? Nat "breeding_males"
    let females ← doc.getObjValAs? Nat "breeding_females"
    return .unequalSex males females
  else if quantity == "variance" then do
    let p ← rat doc "allele_frequency"
    let v ← rat doc "frequency_variance"
    return .variance p v
  else if quantity == "offspring_variance" then do
    let copies ← doc.getObjValAs? Nat "gene_copies"
    let sigma2 ← rat doc "offspring_variance"
    return .offspring copies sigma2
  else throw "unsupported quantity"

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-effective-size-v1" then
    throw "unsupported schema"
  let quantity ← doc.getObjValAs? String "quantity"
  let inputs ← query doc quantity
  let claim ← rat doc "effective_size"
  return ⟨inputs, claim⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, 1)
    else .error "unsupported effective-size request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-effective-size-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def encodeRats (values : List Rat) : Json := .arr (values.toArray.map encodeRat)

def Query.fields : Query → List (String × Json)
  | .harmonic sizes => [("sizes", encodeRats sizes)]
  | .unequalSex males females =>
    [("breeding_males", toJson males), ("breeding_females", toJson females)]
  | .variance p v => [("allele_frequency", encodeRat p), ("frequency_variance", encodeRat v)]
  | .offspring copies sigma2 =>
    [("gene_copies", toJson copies), ("offspring_variance", encodeRat sigma2)]

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-effective-size-v1"), ("quantity", .str r.query.name),
    ("effective_size", encodeRat r.claim)] ++ r.query.fields

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.EffectiveSizeWire
