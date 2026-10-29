/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.FStatistics
public import Rhone.Computation.ParamsWire

/-! # JSON AST surface of the F-statistics comparison -/

@[expose] public section
namespace Rhone.Computation.FStatisticsWire
open Lean

structure Request where
  demes : List (Rat × Rat)
  observed : Rat
  subpopulation : Rat
  total : Rat
  fIS : Rat
  fST : Rat
  fIT : Rat
  deficit : Rat
  varianceForm : Rat
  fSTWahlund : Rat

def Request.claim (r : Request) : Array Rat :=
  #[r.subpopulation, r.total, r.fIS, r.fST, r.fIT, r.deficit, r.varianceForm, r.fSTWahlund]

def Request.valid (r : Request) : Bool :=
  decide (FStatistics.weightsNormalized r.demes = true ∧ FStatistics.meanHet r.demes ≠ 0 ∧
    FStatistics.pooledHet r.demes ≠ 0 ∧ r.demes.length ≤ 4096)

def Request.check (r : Request) : Bool :=
  decide (r.subpopulation = FStatistics.meanHet r.demes ∧
    r.total = FStatistics.pooledHet r.demes ∧
    FStatistics.fStatistics r.observed (FStatistics.meanHet r.demes)
      (FStatistics.pooledHet r.demes) = some (r.fIS, r.fST, r.fIT) ∧
    FStatistics.wahlundDeficit r.demes = some r.deficit ∧
    FStatistics.wahlundVarianceForm r.demes = some r.varianceForm ∧
    FStatistics.fStWahlund r.demes = some r.fSTWahlund)

def Request.ofFormula (demes : List (Rat × Rat)) (observed : Rat) : Request :=
  let f := (FStatistics.fStatistics observed (FStatistics.meanHet demes)
    (FStatistics.pooledHet demes)).getD (0, 0, 0)
  ⟨demes, observed, FStatistics.meanHet demes, FStatistics.pooledHet demes, f.1, f.2.1, f.2.2,
    (FStatistics.wahlundDeficit demes).getD 0, (FStatistics.wahlundVarianceForm demes).getD 0,
    (FStatistics.fStWahlund demes).getD 0⟩

def rat (object : Json) (name : String) : Except String Rat :=
  (object.getObjValAs? String name).bind RationalWire.decode

def deme (entry : Json) : Except String (Rat × Rat) := do
  let weight ← rat entry "weight"
  let frequency ← rat entry "frequency"
  return (weight, frequency)

def demeArray (value : Json) : Except String (Array (Rat × Rat)) :=
  value.getArr?.bind fun entries => entries.mapM deme

def decode (doc : Json) : Except String Request := do
  if (← doc.getObjValAs? String "schema") != "rhone-f-statistics-v1" then
    throw "unsupported schema"
  let demes ← (doc.getObjVal? "demes").bind demeArray
  let observed ← rat doc "observed_heterozygosity"
  let subpopulation ← rat doc "subpopulation_heterozygosity"
  let total ← rat doc "total_heterozygosity"
  let fIS ← rat doc "f_is"
  let fST ← rat doc "f_st"
  let fIT ← rat doc "f_it"
  let deficit ← rat doc "wahlund_deficit"
  let varianceForm ← rat doc "wahlund_variance_form"
  let fSTWahlund ← rat doc "f_st_wahlund"
  return ⟨demes.toList, observed, subpopulation, total, fIS, fST, fIT, deficit, varianceForm,
    fSTWahlund⟩

def decision (doc : Json) : Except String (Bool × Nat) :=
  match decode doc with
  | .error message => .error message
  | .ok r =>
    if r.valid then .ok (r.check, r.claim.size)
    else .error "unsupported F-statistics request domain"

def stamp (decision : Bool × Nat) : Json :=
  Json.mkObj [("schema", toJson "rhone-compute-f-statistics-check-v1"),
    ("accepted", toJson decision.1), ("checked_rational_values", toJson decision.2),
    ("json_boundary_equality_proved", toJson false),
    ("rust_implementation_equality_proved", toJson false)]

def requestAst (doc : Json) : Except String Json := (decision doc).map stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

def encodeRat (value : Rat) : Json := .str (RationalWire.strictPrint value)

def demeFields (d : Rat × Rat) : List (String × Json) :=
  [("weight", encodeRat d.1), ("frequency", encodeRat d.2)]

def encodeDeme (d : Rat × Rat) : Json := Json.mkObj (demeFields d)

def encodeDemes (demes : List (Rat × Rat)) : Json := .arr (demes.toArray.map encodeDeme)

def requestFields (r : Request) : List (String × Json) :=
  [("schema", toJson "rhone-f-statistics-v1"), ("demes", encodeDemes r.demes),
    ("observed_heterozygosity", encodeRat r.observed),
    ("subpopulation_heterozygosity", encodeRat r.subpopulation),
    ("total_heterozygosity", encodeRat r.total),
    ("f_is", encodeRat r.fIS), ("f_st", encodeRat r.fST), ("f_it", encodeRat r.fIT),
    ("wahlund_deficit", encodeRat r.deficit),
    ("wahlund_variance_form", encodeRat r.varianceForm),
    ("f_st_wahlund", encodeRat r.fSTWahlund)]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.FStatisticsWire
