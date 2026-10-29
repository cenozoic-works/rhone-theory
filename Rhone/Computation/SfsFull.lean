/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SfsWire
public import Rhone.Computation.SfsObserved

/-!
# Complete SFS report reader, including optional observed counts

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thm 1.22; fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Computation.SfsFull
open Lean

structure Observed where
  counts : Array Nat
  segregating : Rat
  watterson : Rat
  pairwise : Rat

def Observed.claim (o : Observed) : Array Rat :=
  #[o.segregating, o.watterson, o.pairwise]

structure Request where
  base : SfsWire.Request
  inputCounts : Option (Array Nat)
  observed : Option Observed

def Request.valid (r : Request) : Bool :=
  r.base.valid && match r.inputCounts, r.observed with
    | none, none => true
    | some counts, some o =>
      decide (counts.size = r.base.geneCopies - 1 ∧ o.counts.size = counts.size)
    | _, _ => false

def Request.check (r : Request) : Bool :=
  Sfs.checkReport r.base.geneCopies r.base.theta r.base.claim &&
    match r.inputCounts, r.observed with
    | none, none => true
    | some counts, some o => decide (o.counts = counts) &&
      decide (o.claim = SfsObserved.values r.base.geneCopies counts)
    | _, _ => false

def Request.rationalCount (r : Request) : Nat :=
  r.base.claim.size + if r.observed.isSome then 3 else 0

def Request.binCount (r : Request) : Nat :=
  match r.inputCounts with | none => 0 | some counts => counts.size

def optionalField (doc : Json) (name : String) : Json :=
  match doc.getObjVal? name with | .error _ => .null | .ok value => value

def fieldsAllowed (value : Json) (allowed : List String) : Except String Unit := do
  let fields ← value.getObj?
  if fields.toList.all (fun p => allowed.contains p.1) then return ()
  else throw "unsupported SFS report field"

def reportKeys : List String :=
  ["schema", "model", "comparison_semantics", "gene_copies", "theta",
    "mutation_rate_per_lineage", "coalescence_rate_per_pair", "coefficients",
    "expected_spectrum", "null_moments", "observed", "specification", "implementation",
    "assumptions", "not_computed", "rhone_version", "provenance"]

def coefficientKeys : List String := ["a1", "a2", "b1", "b2"]

def momentKeys : List String :=
  ["mean_segregating", "variance_segregating", "mean_pairwise",
    "second_moment_pairwise", "variance_pairwise"]

def binKeys : List String := ["derived_copies", "mean"]

def observedKeys : List String := ["unfolded_counts", "segregating", "watterson", "pairwise"]

def nullFieldsAllowed (report : Json) : Except String Unit := do
  fieldsAllowed report reportKeys
  let coefficients ← report.getObjVal? "coefficients"
  fieldsAllowed coefficients coefficientKeys
  let moments ← report.getObjVal? "null_moments"
  fieldsAllowed moments momentKeys
  let bins ← (report.getObjVal? "expected_spectrum").bind Json.getArr?
  if !(bins.all (fun b => (fieldsAllowed b binKeys).toOption.isSome)) then
    throw "unsupported SFS bin field"

def natArray (value : Json) : Except String (Array Nat) := do
  let entries ← value.getArr?
  entries.mapM Json.getNat?

def inputCounts (value : Json) : Except String (Option (Array Nat)) :=
  match value with | .null => .ok none | _ => (natArray value).map some

def observed (value : Json) : Except String (Option Observed) := do
  match value with
  | .null => return none
  | _ =>
    fieldsAllowed value observedKeys
    let counts ← (value.getObjVal? "unfolded_counts").bind natArray
    let segregating ← SfsWire.rat value "segregating"
    let watterson ← SfsWire.rat value "watterson"
    let pairwise ← SfsWire.rat value "pairwise"
    return some ⟨counts, segregating, watterson, pairwise⟩

def decode (doc : Json) : Except String Request := do
  let op ← doc.getObjValAs? String "op"
  if op != "check_sfs" then throw "wrong SFS operation"
  let base ← SfsWire.decode doc
  let counts ← inputCounts (optionalField doc "counts")
  let report ← doc.getObjVal? "report"
  nullFieldsAllowed report
  let model ← report.getObjValAs? String "model"
  let mutation ← report.getObjValAs? String "mutation_rate_per_lineage"
  let coalescence ← report.getObjValAs? String "coalescence_rate_per_pair"
  if model != "kingman_constant_size_infinite_sites" || mutation != "theta/2" ||
      coalescence != "1/1" then throw "wrong SFS model or rate conventions"
  let obs ← observed (optionalField report "observed")
  return ⟨base, counts, obs⟩

def decision (doc : Json) : Except String (Bool × Nat × Nat) :=
  match decode doc with
  | .error e => .error e
  | .ok r => if r.valid then .ok (r.check, r.rationalCount, r.binCount)
    else .error "unsupported sample, theta, or observed count shape"

def stamp (d : Bool × Nat × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-kernel-sfs-full-check-v1"),
    ("accepted", toJson d.1), ("checked_rational_values", toJson d.2.1),
    ("checked_observed_bins", toJson d.2.2),
    ("checker", toJson "Rhone.Computation.SfsFull.Request.check"),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json := Json.parse line >>= requestAst

def Observed.ofCounts (n : Nat) (counts : Array Nat) : Observed :=
  ⟨counts, SfsObserved.total counts, Sfs.watterson n (SfsObserved.total counts),
    SfsObserved.pairwise n counts⟩

def Request.ofFormula (n : Nat) (theta : Rat) (counts : Option (Array Nat)) : Request :=
  ⟨SfsWire.Request.ofFormula n theta, counts, counts.map (Observed.ofCounts n)⟩

def observedFields (o : Observed) : List (String × Json) :=
  [("unfolded_counts", .arr (o.counts.map toJson)),
    ("segregating", .str (RationalWire.strictPrint o.segregating)),
    ("watterson", .str (RationalWire.strictPrint o.watterson)),
    ("pairwise", .str (RationalWire.strictPrint o.pairwise))]

def encodeObserved (o : Option Observed) : Json :=
  match o with | none => .null | some value => Json.mkObj (observedFields value)

def reportFields (r : Request) : List (String × Json) :=
  SfsWire.reportFields r.base ++
    [("model", toJson "kingman_constant_size_infinite_sites"),
      ("mutation_rate_per_lineage", toJson "theta/2"),
      ("coalescence_rate_per_pair", toJson "1/1"),
      ("observed", encodeObserved r.observed)]

def requestFields (r : Request) : List (String × Json) :=
  [("op", toJson "check_sfs"), ("gene_copies", toJson r.base.geneCopies),
    ("theta", .str (RationalWire.strictPrint r.base.theta)),
    ("counts", match r.inputCounts with | none => .null | some c => .arr (c.map toJson)),
    ("report", Json.mkObj (reportFields r))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.SfsFull
