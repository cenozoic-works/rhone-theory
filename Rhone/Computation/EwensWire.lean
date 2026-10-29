/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Ewens
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the Ewens sampling comparison -/

@[expose] public section
namespace Rhone.Computation.EwensWire
open Lean

structure Request where
  theta : Rat
  parts : List Nat
  partitionProbability : Rat
  alleleCountProbability : Rat
  expectedAlleles : Rat

def Request.claim (r : Request) : Array Rat :=
  #[r.partitionProbability, r.alleleCountProbability, r.expectedAlleles]

def Request.valid (r : Request) : Bool :=
  decide (0 < r.theta ∧ (∀ x ∈ r.parts, 0 < x) ∧ r.parts.sum ≤ 1024)

def Request.check (r : Request) : Bool :=
  decide (Ewens.esf r.theta r.parts = some r.partitionProbability ∧
    Ewens.alleleCountProb r.theta r.parts.sum r.parts.length =
      some r.alleleCountProbability ∧
    Ewens.expectedAlleles r.theta r.parts.sum = some r.expectedAlleles)

def Request.ofFormula (theta : Rat) (parts : List Nat) : Request :=
  ⟨theta, parts, (Ewens.esf theta parts).getD 0,
    (Ewens.alleleCountProb theta parts.sum parts.length).getD 0,
    (Ewens.expectedAlleles theta parts.sum).getD 0⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def natArray (value : Json) : Except String (Array Nat) :=
  value.getArr?.bind fun entries => entries.mapM Json.getNat?

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-ewens-v1" then
    throw "unsupported schema"
  let theta ← rat doc "theta"
  let parts ← (doc.getObjVal? "partition").bind natArray
  let partition ← rat doc "partition_probability"
  let count ← rat doc "allele_count_probability"
  let expected ← rat doc "expected_alleles"
  return ⟨theta, parts.toList, partition, count, expected⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.claim.size)
    else .error "unsupported Ewens request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-ewens-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def encodeNats (values : List Nat) : Json := .arr (values.toArray.map toJson)

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-ewens-v1"), ("theta", encodeRat r.theta),
    ("partition", encodeNats r.parts),
    ("partition_probability", encodeRat r.partitionProbability),
    ("allele_count_probability", encodeRat r.alleleCountProbability),
    ("expected_alleles", encodeRat r.expectedAlleles)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.EwensWire
