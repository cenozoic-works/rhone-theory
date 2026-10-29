/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SfsCheck
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the `check_sfs` request -/

@[expose] public section
namespace Rhone.Computation.SfsWire
open Lean

structure Request where
  geneCopies : Nat
  theta : Rat
  a1 : Rat
  a2 : Rat
  b1 : Rat
  b2 : Rat
  meanSegregating : Rat
  varianceSegregating : Rat
  meanPairwise : Rat
  secondMomentPairwise : Rat
  variancePairwise : Rat
  spectrum : Array Rat

def Request.claim (r : Request) : Array Rat :=
  #[r.a1, r.a2, r.b1, r.b2, r.meanSegregating, r.varianceSegregating,
    r.meanPairwise, r.secondMomentPairwise, r.variancePairwise] ++ r.spectrum

def Request.valid (r : Request) : Bool :=
  decide (2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta)

def Request.ofFormula (n : Nat) (theta : Rat) : Request :=
  let c := Sfs.coefficients n
  let m := Sfs.moments n theta
  ⟨n, theta, c.a1, c.a2, c.b1, c.b2, m.meanSegregating, m.varianceSegregating,
    m.meanPairwise, m.secondMomentPairwise, m.variancePairwise, Sfs.spectrum n theta⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def bin (entry : Json × Nat) : Except String Rat := do
  if (← entry.1.getObjValAs? Nat "derived_copies") != entry.2 + 1 then
    throw "noncanonical derived-copy bin order"
  rat entry.1 "mean"

def decode (doc : Json) : Except String Request := do
  let n ← doc.getObjValAs? Nat "gene_copies"
  let theta ← rat doc "theta"
  let report ← doc.getObjVal? "report"
  if (← report.getObjValAs? String "schema") != "rhone-sfs-v1" then
    throw "unsupported report schema"
  if (← report.getObjValAs? Nat "gene_copies") != n then
    throw "report sample size differs from the request"
  if (← rat report "theta") != theta then throw "report theta differs from the request"
  let coefficients ← report.getObjVal? "coefficients"
  let moments ← report.getObjVal? "null_moments"
  let a1 ← rat coefficients "a1"
  let a2 ← rat coefficients "a2"
  let b1 ← rat coefficients "b1"
  let b2 ← rat coefficients "b2"
  let meanSegregating ← rat moments "mean_segregating"
  let varianceSegregating ← rat moments "variance_segregating"
  let meanPairwise ← rat moments "mean_pairwise"
  let secondMomentPairwise ← rat moments "second_moment_pairwise"
  let variancePairwise ← rat moments "variance_pairwise"
  let bins ← (report.getObjVal? "expected_spectrum").bind Json.getArr?
  let spectrum ← bins.zipIdx.mapM bin
  return ⟨n, theta, a1, a2, b1, b2, meanSegregating, varianceSegregating, meanPairwise,
    secondMomentPairwise, variancePairwise, spectrum⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (Sfs.checkReport r.geneCopies r.theta r.claim, r.claim.size)
    else .error "unsupported sample size or negative theta"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-kernel-sfs-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("checker", toJson "Rhone.Computation.Sfs.checkReport"),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def binFields (entry : Rat × Nat) : List (String × Json) :=
  [("derived_copies", toJson (entry.2 + 1)),
    ("mean", .str (RationalWire.strictPrint entry.1))]

def encodeBin (entry : Rat × Nat) : Json := Json.mkObj (binFields entry)

def coefficientFields (r : Request) : List (String × Json) :=
  [("a1", .str (RationalWire.strictPrint r.a1)), ("a2", .str (RationalWire.strictPrint r.a2)),
    ("b1", .str (RationalWire.strictPrint r.b1)), ("b2", .str (RationalWire.strictPrint r.b2))]

def momentFields (r : Request) : List (String × Json) :=
  [("mean_segregating", .str (RationalWire.strictPrint r.meanSegregating)),
    ("variance_segregating", .str (RationalWire.strictPrint r.varianceSegregating)),
    ("mean_pairwise", .str (RationalWire.strictPrint r.meanPairwise)),
    ("second_moment_pairwise", .str (RationalWire.strictPrint r.secondMomentPairwise)),
    ("variance_pairwise", .str (RationalWire.strictPrint r.variancePairwise))]

def reportFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-sfs-v1"), ("gene_copies", toJson r.geneCopies),
    ("theta", .str (RationalWire.strictPrint r.theta)),
    ("coefficients", Json.mkObj (coefficientFields r)),
    ("null_moments", Json.mkObj (momentFields r)),
    ("expected_spectrum", .arr (r.spectrum.zipIdx.map encodeBin))]

def requestFields (r : Request) : List (String × Json) :=
  [("op", toJson "check_sfs"), ("gene_copies", toJson r.geneCopies),
    ("theta", .str (RationalWire.strictPrint r.theta)),
    ("report", Json.mkObj (reportFields r))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.SfsWire
