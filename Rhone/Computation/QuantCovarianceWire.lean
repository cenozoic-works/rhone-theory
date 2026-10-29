/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.QuantCovariance
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the single-locus variance and covariance comparison -/

@[expose] public section
namespace Rhone.Computation.QuantCovarianceWire
open Lean

structure Request where
  frequency : Rat
  g0 : Rat
  g1 : Rat
  g2 : Rat
  additiveVariance : Rat
  dominanceVariance : Rat
  parentOffspring : Rat
  halfSib : Rat
  fullSib : Rat

def Request.values (r : Request) : QuantCovariance.Values := ⟨r.g0, r.g1, r.g2⟩

def Request.claim (r : Request) : Array Rat :=
  #[r.additiveVariance, r.dominanceVariance, r.parentOffspring, r.halfSib, r.fullSib]

def Request.valid (r : Request) : Bool := QuantCovariance.validFreq r.frequency

def Request.check (r : Request) : Bool :=
  decide (QuantCovariance.varA r.frequency r.values = some r.additiveVariance ∧
    QuantCovariance.varD r.frequency r.values = some r.dominanceVariance ∧
    QuantCovariance.parentOffspringCov r.frequency r.values = some r.parentOffspring ∧
    QuantCovariance.halfSibCov r.frequency r.values = some r.halfSib ∧
    QuantCovariance.fullSibCov r.frequency r.values = some r.fullSib)

def Request.ofFormula (p g0 g1 g2 : Rat) : Request :=
  ⟨p, g0, g1, g2, (QuantCovariance.varA p ⟨g0, g1, g2⟩).getD 0,
    (QuantCovariance.varD p ⟨g0, g1, g2⟩).getD 0,
    (QuantCovariance.parentOffspringCov p ⟨g0, g1, g2⟩).getD 0,
    (QuantCovariance.halfSibCov p ⟨g0, g1, g2⟩).getD 0,
    (QuantCovariance.fullSibCov p ⟨g0, g1, g2⟩).getD 0⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-quant-covariance-v1" then
    throw "unsupported schema"
  let p ← rat doc "allele_frequency"
  let g0 ← rat doc "genotypic_value_0"
  let g1 ← rat doc "genotypic_value_1"
  let g2 ← rat doc "genotypic_value_2"
  let additive ← rat doc "additive_variance"
  let dominance ← rat doc "dominance_variance"
  let parentOffspring ← rat doc "parent_offspring_covariance"
  let halfSib ← rat doc "half_sib_covariance"
  let fullSib ← rat doc "full_sib_covariance"
  return ⟨p, g0, g1, g2, additive, dominance, parentOffspring, halfSib, fullSib⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.claim.size)
    else .error "unsupported quantitative covariance request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-quant-covariance-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-quant-covariance-v1"),
    ("allele_frequency", encodeRat r.frequency),
    ("genotypic_value_0", encodeRat r.g0), ("genotypic_value_1", encodeRat r.g1),
    ("genotypic_value_2", encodeRat r.g2),
    ("additive_variance", encodeRat r.additiveVariance),
    ("dominance_variance", encodeRat r.dominanceVariance),
    ("parent_offspring_covariance", encodeRat r.parentOffspring),
    ("half_sib_covariance", encodeRat r.halfSib),
    ("full_sib_covariance", encodeRat r.fullSib)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.QuantCovarianceWire
