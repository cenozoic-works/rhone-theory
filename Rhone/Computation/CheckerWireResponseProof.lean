/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWire
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Rhone.Computation.ParamsWireTypedProof

/-! # Checker AST refusal and response fidelity -/

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


theorem response_ok (result : Json) : response (.ok result) = result := rfl

theorem response_error (error : String) : response (.error error) =
    stamp [("accepted", toJson false), ("error", toJson error)] := rfl

theorem request_parse_error (line error : String) (h : Json.parse line = .error error) :
    request line = .error error := by
  simp only [request, h, error_bind]

theorem requestAst_wrong_operation (doc : Json) (operation : String)
    (hop : doc.getObjValAs? String "op" = .ok operation)
    (hwrong : operation ≠ "check_table") :
    requestAst doc = .error "unsupported operation" := by
  simp [requestAst, hop, hwrong]

theorem requestAst_large_bound (doc : Json) (n : Nat)
    (hop : doc.getObjValAs? String "op" = .ok "check_table")
    (hbound : doc.getObjValAs? Nat "n" = .ok n) (hn : 65535 < n) :
    requestAst doc = .error "unsupported bound: exceeds the u16 configuration wire domain" := by
  simp [requestAst, hop, hbound, hn]

theorem requestAst_invalid_parameters (doc : Json) (n : Nat) (p : Params)
    (hop : doc.getObjValAs? String "op" = .ok "check_table")
    (hbound : doc.getObjValAs? Nat "n" = .ok n) (hn : n ≤ 65535)
    (hparams : ParamsWire.decodeTyped doc = .ok p) (hp : p.valid = false) :
    requestAst doc = .error "invalid parameter domain" := by
  simp [requestAst, hop, hbound, Nat.not_lt_of_ge hn, hparams, hp]

theorem requestAst_congr {a b : Json}
    (hop : a.getObjValAs? String "op" = b.getObjValAs? String "op")
    (hn : a.getObjValAs? Nat "n" = b.getObjValAs? Nat "n")
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b")
    (hentries : a.getObjVal? "entries" = b.getObjVal? "entries") :
    requestAst a = requestAst b := by
  have hp := ParamsWire.decodeTyped_congr hθA hθB hρ hπA hπB
  simp only [requestAst, hop, hn, hp, hentries]

theorem response_requestAst_congr {a b : Json}
    (hop : a.getObjValAs? String "op" = b.getObjValAs? String "op")
    (hn : a.getObjValAs? Nat "n" = b.getObjValAs? Nat "n")
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b")
    (hentries : a.getObjVal? "entries" = b.getObjVal? "entries") :
    response (requestAst a) = response (requestAst b) :=
  congrArg response (requestAst_congr hop hn hθA hθB hρ hπA hπB hentries)

theorem request_congr (x y : String) {a b : Json}
    (hx : Json.parse x = .ok a) (hy : Json.parse y = .ok b)
    (hop : a.getObjValAs? String "op" = b.getObjValAs? String "op")
    (hn : a.getObjValAs? Nat "n" = b.getObjValAs? Nat "n")
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b")
    (hentries : a.getObjVal? "entries" = b.getObjVal? "entries") :
    request x = request y := by
  simp only [request, hx, hy, ok_bind]
  exact requestAst_congr hop hn hθA hθB hρ hπA hπB hentries

theorem response_request_congr (x y : String) {a b : Json}
    (hx : Json.parse x = .ok a) (hy : Json.parse y = .ok b)
    (hop : a.getObjValAs? String "op" = b.getObjValAs? String "op")
    (hn : a.getObjValAs? Nat "n" = b.getObjValAs? Nat "n")
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b")
    (hentries : a.getObjVal? "entries" = b.getObjVal? "entries") :
    response (request x) = response (request y) :=
  congrArg response (request_congr x y hx hy hop hn hθA hθB hρ hπA hπB hentries)

end Rhone.Computation.CheckerWire
