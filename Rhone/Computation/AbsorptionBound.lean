/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.AbsorptionWire

/-! # Absorption report compared with the inputs of the caller -/

@[expose] public section
namespace Rhone.Computation.AbsorptionBound
open Lean

structure Inputs where
  moran : Bool
  geneCopies : Nat
  initialCount : Nat
  fitness : Rat
  provenance : String

structure Request where
  inputs : Inputs
  report : AbsorptionWire.Request

def Request.bound (r : Request) : Bool :=
  decide (r.report.moran = r.inputs.moran ∧ r.report.geneCopies = r.inputs.geneCopies ∧
    r.report.initialCount = r.inputs.initialCount ∧ r.report.fitness = r.inputs.fitness ∧
    r.report.provenance = r.inputs.provenance)

def wfFitness : Json → Except String (Bool × Rat)
  | .null => .ok (false, 1)
  | _ => .error "invalid WF convention"

def inputModel (doc : Json) (model : String) : Except String (Bool × Rat) :=
  if model == "wright-fisher" then (doc.getObjVal? "relative_fitness").bind wfFitness
  else if model == "moran" then
    (AbsorptionWire.rat doc "relative_fitness").map fun fitness => (true, fitness)
  else .error "unsupported model"

def decodeInputs (doc : Json) : Except String Inputs := do
  let model ← doc.getObjValAs? String "model"
  let n ← doc.getObjValAs? Nat "gene_copies"
  let i ← doc.getObjValAs? Nat "initial_count"
  let provenance ← doc.getObjValAs? String "parameter_provenance"
  let fields ← inputModel doc model
  return ⟨fields.1, n, i, fields.2, provenance⟩

def decode (doc : Json) : Except String Request := do
  let inputs ← decodeInputs doc
  let report ← (doc.getObjVal? "report").bind AbsorptionWire.decode
  return ⟨inputs, report⟩

def decision (doc : Json) : Except String (Bool × Nat × Bool) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.report.valid then .ok (r.bound && r.report.check, r.report.claimed, r.bound)
    else .error "unsupported absorption request domain"

def stamp (decision : Bool × Nat × Bool) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-absorption-bound-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2.1),
    ("inputs_match", toJson decision.2.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def requestFields (r : Request) : List (String × Json) :=
  [("model", .str (if r.inputs.moran then "moran" else "wright-fisher")),
    ("gene_copies", toJson r.inputs.geneCopies),
    ("initial_count", toJson r.inputs.initialCount),
    ("relative_fitness",
      if r.inputs.moran then AbsorptionWire.encodeEntry r.inputs.fitness else .null),
    ("parameter_provenance", .str r.inputs.provenance),
    ("report", AbsorptionWire.encode r.report)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.AbsorptionBound
