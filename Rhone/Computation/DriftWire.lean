/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftCheck
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the drift report comparison -/

@[expose] public section
namespace Rhone.Computation.DriftWire
open Lean

structure Request where
  moran : Bool
  geneCopies : Nat
  initialCount : Nat
  steps : Nat
  fitness : Rat
  row : Array Rat
  fixation : Rat
  heterozygosity : Option Rat

def Request.neutral (r : Request) : Bool := !r.moran || r.fitness == 1

def Request.claim (r : Request) : Array Rat :=
  r.row ++ #[r.fixation] ++
    (match r.heterozygosity with
    | some value => #[value]
    | none => #[])

def Request.valid (r : Request) : Bool :=
  decide (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 64 ∧ r.initialCount ≤ r.geneCopies ∧
    r.steps ≤ 256 ∧ (r.moran = true → 0 < r.fitness))

def Request.Canonical (r : Request) : Prop :=
  (r.moran = false → r.fitness = 1) ∧ r.heterozygosity.isSome = r.neutral

def Request.check (r : Request) : Bool :=
  if r.moran then Drift.checkMoranReport r.geneCopies r.fitness r.initialCount r.steps r.claim
  else Drift.checkWfReport r.geneCopies r.initialCount r.steps r.claim

def Request.wfFormula (n i t : Nat) : Request :=
  ⟨false, n, i, t, 1, Drift.wfTransition n i, Drift.neutralFixation n i,
    some (Drift.wfHeterozygosity n i t)⟩

def Request.moranFormula (n : Nat) (fitness : Rat) (i t : Nat) : Request :=
  ⟨true, n, i, t, fitness, Drift.moranTransition n fitness i, Drift.moranFixation n fitness i,
    if fitness = 1 then some (Drift.moranHeterozygosity n i t) else none⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def rowEntry (entry : Json) : Except String Rat :=
  entry.getStr?.bind RationalWire.decode

def modelFields (doc : Json) (model : String) : Except String (Bool × Rat) :=
  if model == "wright-fisher" then do
    match (← doc.getObjVal? "relative_fitness") with
    | .null => pure ()
    | _ => throw "WF relative fitness must be null"
    if (← doc.getObjValAs? String "time_unit") != "generation" then
      throw "wrong WF time unit"
    return (false, 1)
  else if model == "moran" then do
    if (← doc.getObjValAs? String "time_unit") != "birth-death-event" then
      throw "wrong Moran time unit"
    let fitness ← rat doc "relative_fitness"
    return (true, fitness)
  else throw "unsupported model"

def heterozygosityField (doc : Json) (neutral : Bool) : Except String (Option Rat) :=
  if neutral then (rat doc "expected_heterozygosity").map some else .ok none

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-drift-v1" then
    throw "unsupported schema"
  if (← doc.getObjValAs? String "comparison_semantics") != "exact_fraction" then
    throw "unsupported comparison semantics"
  let model ← doc.getObjValAs? String "model"
  let n ← doc.getObjValAs? Nat "gene_copies"
  let i ← doc.getObjValAs? Nat "initial_count"
  let t ← doc.getObjValAs? Nat "steps"
  let fields ← modelFields doc model
  if (← doc.getObjValAs? String "heterozygosity_sampling") != "with-replacement" then
    throw "wrong pair-sampling convention"
  let entries ← (doc.getObjVal? "transition_row").bind Json.getArr?
  let row ← entries.mapM rowEntry
  let fixation ← rat doc "fixation_probability"
  let heterozygosity ← heterozygosityField doc (!fields.1 || fields.2 == 1)
  return ⟨fields.1, n, i, t, fields.2, row, fixation, heterozygosity⟩

def decision (doc : Json) : Except String (Bool × Nat × Bool) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.claim.size, r.neutral)
    else .error "unsupported drift request domain"

def stamp (decision : Bool × Nat × Bool) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-drift-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2.1),
    ("neutral_heterozygosity_checked", toJson decision.2.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeEntry (value : Rat) : Json := .str (RationalWire.strictPrint value)

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-drift-v1"), ("comparison_semantics", toJson "exact_fraction"),
    ("model", .str (if r.moran then "moran" else "wright-fisher")),
    ("gene_copies", toJson r.geneCopies), ("initial_count", toJson r.initialCount),
    ("steps", toJson r.steps),
    ("relative_fitness", if r.moran then encodeEntry r.fitness else .null),
    ("time_unit", .str (if r.moran then "birth-death-event" else "generation")),
    ("heterozygosity_sampling", toJson "with-replacement"),
    ("transition_row", .arr (r.row.map encodeEntry)),
    ("fixation_probability", encodeEntry r.fixation),
    ("expected_heterozygosity",
      match r.heterozygosity with
      | some value => encodeEntry value
      | none => .null)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.DriftWire
