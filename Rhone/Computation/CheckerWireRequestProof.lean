/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWireEntryProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Rhone.Computation.ParamsWireTypedProof

/-! # Exact finite-table request AST fidelity -/

@[expose] public section
namespace Rhone.Computation.CheckerWire
open Lean

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl

@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

@[simp] private theorem map_ok {α β : Type} (x : α) (f : α → β) :
    f <$> (Except.ok x : Except String α) = Except.ok (f x) := rfl

@[simp] private theorem map_error {α β : Type} (e : String) (f : α → β) :
    f <$> (Except.error e : Except String α) = Except.error e := rfl


private theorem encodeRequest_getObjVal {p : Params} {n : Nat}
    {rows : Array (Config × Rat)} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields p n rows) :
    (encodeRequest p n rows).getObjVal? name = .ok value := by
  have hd : (requestFields p n rows).Pairwise
      (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields, ParamsWire.fields]
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList (requestFields p n rows) compare).get? name =
    some value at hl
  change (match (Std.TreeMap.Raw.ofList (requestFields p n rows) compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

private theorem request_parameter_getters (p : Params) (n : Nat)
    (rows : Array (Config × Rat)) {name : String} {value : Json}
    (hmem : (name, value) ∈ ParamsWire.fields p) :
    (encodeRequest p n rows).getObjVal? name = (ParamsWire.encode p).getObjVal? name := by
  rw [encodeRequest_getObjVal (value := value) (by simp [requestFields, hmem]),
    ParamsWire.encode_getObjVal hmem]

theorem decode_request_parameters (p : Params) (n : Nat)
    (rows : Array (Config × Rat)) :
    ParamsWire.decodeTyped (encodeRequest p n rows) = .ok p := by
  have hθA := request_parameter_getters p n rows
    (by simp [ParamsWire.fields] :
      ("theta_a", Json.str (RationalWire.strictPrint p.thetaA)) ∈ ParamsWire.fields p)
  have hθB := request_parameter_getters p n rows
    (by simp [ParamsWire.fields] :
      ("theta_b", Json.str (RationalWire.strictPrint p.thetaB)) ∈ ParamsWire.fields p)
  have hρ := request_parameter_getters p n rows
    (by simp [ParamsWire.fields] :
      ("rho", Json.str (RationalWire.strictPrint p.rho)) ∈ ParamsWire.fields p)
  have hπA := request_parameter_getters p n rows
    (by simp [ParamsWire.fields] :
      ("pi_a", Json.arr (p.piA.map fun r => Json.str (RationalWire.strictPrint r))) ∈
        ParamsWire.fields p)
  have hπB := request_parameter_getters p n rows
    (by simp [ParamsWire.fields] :
      ("pi_b", Json.arr (p.piB.map fun r => Json.str (RationalWire.strictPrint r))) ∈
        ParamsWire.fields p)
  rw [ParamsWire.decodeTyped_congr hθA hθB hρ hπA hπB, ParamsWire.decodeTyped_encode]

theorem requestAst_encode (p : Params) (hp : p.valid = true) (n : Nat)
    (hn : n ≤ 65535) (rows : Array (Config × Rat))
    (hrows : ∀ row ∈ rows, BoundedConfig row.1) :
    requestAst (encodeRequest p n rows) = .ok
      (stamp [("accepted", toJson (checkTable p n rows)),
        ("bound", toJson n), ("row_count", toJson rows.size)]) := by
  have hop := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [requestFields] : ("op", toJson "check_table") ∈ requestFields p n rows)
  have hbound := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [requestFields] : ("n", toJson n) ∈ requestFields p n rows)
  have hentries := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [requestFields] : ("entries", .arr (rows.map encodeEntry)) ∈
      requestFields p n rows)
  have haop : (encodeRequest p n rows).getObjValAs? String "op" = .ok "check_table" := by
    change Json.getStr? (((encodeRequest p n rows).getObjVal? "op").toOption.getD .null) = _
    rw [hop]
    rfl
  have habound : (encodeRequest p n rows).getObjValAs? Nat "n" = .ok n := by
    change Json.getNat? (((encodeRequest p n rows).getObjVal? "n").toOption.getD .null) = _
    rw [hbound]
    rfl
  simp [requestAst, haop, habound, decode_request_parameters,
    hentries, entries_encode rows hrows, hp, Nat.not_lt_of_ge hn]

end Rhone.Computation.CheckerWire
