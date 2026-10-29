/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SmcPrimeTvCheck
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the SMC-prime total-variation bound report -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTvWire
open Lean

structure Request where
  geneCopies : Nat
  intensity : Rat
  doubleBound : Rat
  coefficient : Rat
  quadratic : Rat
  clipped : Rat
  windowId : String
  provenance : String

def Request.claim (r : Request) : Array Rat :=
  #[r.doubleBound, r.coefficient, r.quadratic, r.clipped]

def boundedNonempty (value : String) (limit : Nat) : Bool :=
  !value.trimAscii.toString.isEmpty && decide (value.utf8ByteSize ≤ limit)

def Request.valid (r : Request) : Bool :=
  decide (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 256 ∧ 0 ≤ r.intensity ∧
    (RationalWire.strictPrint r.intensity).utf8ByteSize ≤ 64) &&
    boundedNonempty r.windowId 128 && boundedNonempty r.provenance 512

def Request.ofFormula (n : Nat) (R : Rat) (windowId provenance : String) : Request :=
  ⟨n, R, SmcPrimeTv.doubleBound R (n - 1), SmcPrimeTv.quadraticCoefficient (n - 1),
    SmcPrimeTv.quadraticBound R (n - 1), SmcPrimeTv.clippedQuadraticBound R (n - 1),
    windowId, provenance⟩

def schemaName : String := "rhone-smc-prime-tv-bound-v1"

def modelNames : Array String :=
  #["full_ARG_genealogy_law", "original_SMC_prime_genealogy_law"]

def scopeName : String := "all_rational_genomic_positions_and_labelled_pair_mrca_times"

def parseStrictRat (text : String) : Except String Rat := do
  let value ← RationalWire.decode text
  if RationalWire.strictPrint value != text then throw "noncanonical rational wire value"
  return value

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind parseStrictRat

def exactBounds (bounds : Json) : Except String Unit := do
  let fields ← bounds.getObj?
  if fields.size != 4 then throw "unexpected object field count"
  let _ ← bounds.getObjVal? "double_bound"
  let _ ← bounds.getObjVal? "quadratic_coefficient"
  let _ ← bounds.getObjVal? "quadratic_bound"
  let _ ← bounds.getObjVal? "clipped_quadratic_bound"
  return ()

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != schemaName then throw "unsupported schema"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported arithmetic convention"
  if (← doc.getObjValAs? (Array String) "models") != modelNames then
    throw "unsupported models"
  if (← doc.getObjValAs? String "observation_scope") != scopeName then
    throw "unsupported observation scope"
  let n ← doc.getObjValAs? Nat "gene_copies"
  if (← doc.getObjValAs? Nat "recursion_index") != n - 1 then
    throw "recursion index does not match sample size"
  let intensity ← rat doc "integrated_recombination_intensity"
  let windowId ← doc.getObjValAs? String "window_id"
  let provenance ← doc.getObjValAs? String "model_provenance"
  let bounds ← doc.getObjVal? "bounds"
  exactBounds bounds
  let doubleBound ← rat bounds "double_bound"
  let coefficient ← rat bounds "quadratic_coefficient"
  let quadratic ← rat bounds "quadratic_bound"
  let clipped ← rat bounds "clipped_quadratic_bound"
  return ⟨n, intensity, doubleBound, coefficient, quadratic, clipped, windowId, provenance⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim, r.claim.size)
    else .error "request outside the supported domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-smc-prime-tv-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("checker", toJson "Rhone.Computation.SmcPrimeTv.checkReport"),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def boundFields (r : Request) : List (String × Json) :=
  [("double_bound", .str (RationalWire.strictPrint r.doubleBound)),
    ("quadratic_coefficient", .str (RationalWire.strictPrint r.coefficient)),
    ("quadratic_bound", .str (RationalWire.strictPrint r.quadratic)),
    ("clipped_quadratic_bound", .str (RationalWire.strictPrint r.clipped))]

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson schemaName), ("comparison_semantics", toJson "exact_fraction"),
    ("models", toJson modelNames), ("observation_scope", toJson scopeName),
    ("gene_copies", toJson r.geneCopies), ("recursion_index", toJson (r.geneCopies - 1)),
    ("integrated_recombination_intensity", .str (RationalWire.strictPrint r.intensity)),
    ("window_id", toJson r.windowId), ("model_provenance", toJson r.provenance),
    ("bounds", Json.mkObj (boundFields r))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.SmcPrimeTvWire
