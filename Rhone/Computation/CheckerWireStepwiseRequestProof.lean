/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWire
import all Init.Control.Except

/-! # The checker request decoder agrees with its explicit step-by-step form -/

@[expose] public section
namespace Rhone.Computation.CheckerWire
open Lean

def originalRequestAst (doc : Json) : Except String Json := do
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table" then throw "unsupported operation"
  let bound ← doc.getObjValAs? Nat "n"
  if bound > 65535 then throw "unsupported bound: exceeds the u16 configuration wire domain"
  let getRat := fun name => (doc.getObjValAs? String name).bind RationalWire.decode
  let getPi := fun name => do
    let xs ← (doc.getObjVal? name).bind Json.getArr?
    xs.mapM fun value => value.getStr? >>= RationalWire.decode
  let thetaA ← getRat "theta_a"
  let thetaB ← getRat "theta_b"
  let rho ← getRat "rho"
  let piA ← getPi "pi_a"
  let piB ← getPi "pi_b"
  let params : Params := ⟨thetaA, thetaB, rho, piA, piB⟩
  if !params.valid then throw "invalid parameter domain"
  let rows ← (doc.getObjVal? "entries").bind Json.getArr?
  let entries ← rows.mapM fun row => do
    let key ← row.getObjValAs? String "key"
    let value ← (row.getObjValAs? String "value").bind RationalWire.decode
    let config ← parseConfig key
    return (config, value)
  return stamp [("accepted", toJson (checkTable params bound entries)),
    ("bound", toJson bound), ("row_count", toJson entries.size)]

private theorem explicit_bind_eq {α β : Type} (x : Except String α)
    (f : α → Except String β) : x.bind f = x >>= f := rfl

private theorem rational_callback_eq : ParamsWire.rational =
    (fun value => value.getStr? >>= RationalWire.decode) := rfl

private theorem entry_callback_eq : entry = (fun row => do
    let key ← row.getObjValAs? String "key"
    let value ← row.getObjValAs? String "value" >>= RationalWire.decode
    let config ← parseConfig key
    return (config, value)) := rfl

theorem requestAst_eq_original (doc : Json) :
    requestAst doc = originalRequestAst doc := by
  simp only [requestAst, originalRequestAst, ParamsWire.decodeTyped,
    ParamsWire.typedRationalField, ParamsWire.frequencyField,
    ParamsWire.frequencies, entries, rational_callback_eq, entry_callback_eq,
    explicit_bind_eq, bind_assoc, pure_bind] <;> rfl

end Rhone.Computation.CheckerWire
