/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftWire
public import Rhone.Computation.AbsorptionWire
public import Rhone.Computation.DriftLaw

/-! # Drift report with its distribution, heterozygosity, and absorption time -/

@[expose] public section
namespace Rhone.Computation.DriftFull
open Lean

structure Request where
  base : DriftWire.Request
  distribution : Array Rat
  heterozygosity : Rat
  absorption : Rat
  table : Array Rat

def Request.law (r : Request) : Array Rat :=
  if r.base.moran then
    Drift.moranDistribution r.base.geneCopies r.base.fitness r.base.initialCount r.base.steps
  else Drift.wfDistribution r.base.geneCopies r.base.initialCount r.base.steps

def Request.tableCheck (r : Request) : Bool :=
  if r.base.moran then Absorption.checkMoran r.base.geneCopies r.base.fitness r.table
  else Absorption.checkWf r.base.geneCopies r.table

def Request.check (r : Request) : Bool :=
  let law := r.law
  r.base.check && decide (r.distribution = law) &&
    decide (r.heterozygosity = Drift.lawHeterozygosity r.base.geneCopies law) &&
    r.tableCheck && decide (r.absorption = r.table.getD r.base.initialCount 0)

def Request.count (r : Request) : Nat := r.base.row.size + r.distribution.size + 3

def decode (doc : Json) : Except String Request := do
  let base ← DriftWire.decode doc
  let distribution ← (doc.getObjVal? "distribution").bind AbsorptionWire.ratArray
  let heterozygosity ← DriftWire.rat doc "expected_heterozygosity"
  let absorption ← DriftWire.rat doc "mean_absorption_time"
  let table ← (doc.getObjVal? "mean_absorption_times").bind AbsorptionWire.ratArray
  return ⟨base, distribution, heterozygosity, absorption, table⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.base.valid then .ok (r.check, r.count)
    else .error "unsupported drift request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-drift-full-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.DriftFull
