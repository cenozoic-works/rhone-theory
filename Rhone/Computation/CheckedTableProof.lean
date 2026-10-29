/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckedTable
public import Rhone.Computation.CheckerWireRestrictionProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except

/-! # Meaning of the response line of the closure-based table check -/

@[expose] public section
namespace Rhone.Computation.CheckedTable
open Lean

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl

@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

def IsQTable (p : Params) (rows : Array (Config × Rat)) : Prop :=
  ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
    ∀ entry ∈ rows, entry.2 =
      Rhone.LinearAlgebra.Recursion.q (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
        (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ
        (CheckerEncoding.decode entry.1)

theorem requestAst_eq_decode (doc : Json) :
    CheckerWire.requestAst doc = (decode doc).map fun r =>
      CheckerWire.stamp [("accepted", toJson (checkTable r.params r.bound r.rows)),
        ("bound", toJson r.bound), ("row_count", toJson r.rows.size)] := by
  cases hop : doc.getObjValAs? String "op" with
  | error e => simp [CheckerWire.requestAst, decode, hop, Except.map]
  | ok op =>
    by_cases hopv : op = "check_table"
    · cases hn : doc.getObjValAs? Nat "n" with
      | error e => simp [CheckerWire.requestAst, decode, hop, hopv, hn, Except.map]
      | ok m =>
        by_cases hm : m > 65535
        · simp [CheckerWire.requestAst, decode, hop, hopv, hn, hm, Except.map]
        · cases hp : ParamsWire.decodeTyped doc with
          | error e => simp [CheckerWire.requestAst, decode, hop, hopv, hn, hm, hp, Except.map]
          | ok q =>
            by_cases hv : q.valid = true
            · cases hr : (doc.getObjVal? "entries" >>= CheckerWire.entries) with
              | error e =>
                simp [CheckerWire.requestAst, decode, hop, hopv, hn, hm, hp, hv, hr, Except.map]
              | ok rows =>
                simp [CheckerWire.requestAst, decode, hop, hopv, hn, hm, hp, hv, hr, Except.map]
            · simp [CheckerWire.requestAst, decode, hop, hopv, hn, hm, hp, hv, Except.map]
    · simp [CheckerWire.requestAst, decode, hop, hopv, Except.map]

theorem decode_eq_ok_iff (doc : Json) (r : Request) :
    decode doc = .ok r ↔
      doc.getObjValAs? String "op" = .ok "check_table" ∧
      doc.getObjValAs? Nat "n" = .ok r.bound ∧ r.bound ≤ 65535 ∧
      ParamsWire.decodeTyped doc = .ok r.params ∧ r.params.valid = true ∧
      (doc.getObjVal? "entries" >>= CheckerWire.entries) = .ok r.rows := by
  rcases r with ⟨p, n, rows⟩
  cases hop : doc.getObjValAs? String "op" with
  | error e => simp [decode, hop]
  | ok op =>
    by_cases hopv : op = "check_table"
    · cases hn : doc.getObjValAs? Nat "n" with
      | error e => simp [decode, hop, hopv, hn]
      | ok m =>
        by_cases hm : m > 65535
        · simp [decode, hop, hopv, hn, hm]
          omega
        · cases hp : ParamsWire.decodeTyped doc with
          | error e => simp [decode, hop, hopv, hn, hm, hp]
          | ok q =>
            by_cases hv : q.valid = true
            · cases hr : (doc.getObjVal? "entries" >>= CheckerWire.entries) with
              | error e => simp [decode, hop, hopv, hn, hm, hp, hv, hr]
              | ok rows' =>
                have key : decode doc = .ok ⟨q, m, rows'⟩ := by
                  simp [decode, hop, hopv, hn, hm, hp, hv, hr]
                rw [key]
                constructor
                · intro h
                  cases h
                  exact ⟨by rw [hopv], rfl, Nat.le_of_not_gt hm, rfl, hv, rfl⟩
                · rintro ⟨_, h2, _, h4, _, h6⟩
                  cases h2
                  cases h4
                  cases h6
                  rfl
            · have key : decode doc = .error "invalid parameter domain" := by
                simp [decode, hop, hopv, hn, hm, hp, hv]
              rw [key]
              constructor
              · intro h
                cases h
              · rintro ⟨_, _, _, h4, h5, _⟩
                cases h4
                exact absurd h5 hv
    · simp [decode, hop, hopv]

theorem decode_refuses_iff (doc : Json) :
    (∃ e, decode doc = .error e) ↔ ¬ ∃ r, decode doc = .ok r := by
  cases decode doc <;> simp

theorem respond_accept_iff {ρ : Type} (check : ρ → Bool) (x : Except String ρ) (r : ρ) :
    respond check x = .accept r ↔ x = .ok r ∧ check r = true := by
  cases x with
  | error e => simp [respond]
  | ok a =>
    simp only [respond]
    split
    · rename_i h
      constructor
      · intro hh
        cases hh
        exact ⟨rfl, h⟩
      · rintro ⟨hh, _⟩
        cases hh
        rfl
    · rename_i h
      constructor
      · intro hh
        cases hh
      · rintro ⟨hh, hc⟩
        cases hh
        exact absurd hc h

theorem respond_reject_iff {ρ : Type} (check : ρ → Bool) (x : Except String ρ) (r : ρ) :
    respond check x = .reject r ↔ x = .ok r ∧ check r = false := by
  cases x with
  | error e => simp [respond]
  | ok a =>
    simp only [respond]
    split
    · rename_i h
      constructor
      · intro hh
        cases hh
      · rintro ⟨hh, hc⟩
        cases hh
        rw [h] at hc
        cases hc
    · rename_i h
      constructor
      · intro hh
        cases hh
        exact ⟨rfl, by simpa using h⟩
      · rintro ⟨hh, _⟩
        cases hh
        rfl

theorem respond_refuse_iff {ρ : Type} (check : ρ → Bool) (x : Except String ρ) (e : String) :
    respond check x = .refuse e ↔ x = .error e := by
  cases x with
  | error e' => simp [respond]
  | ok a =>
    simp only [respond]
    split <;> simp

theorem serveAst_accept_iff (doc : Json) (r : Request) :
    serveAst doc = .accept r ↔
      decode doc = .ok r ∧ checkTable r.params r.bound r.rows = true :=
  respond_accept_iff _ _ r

theorem serveAst_reject_iff (doc : Json) (r : Request) :
    serveAst doc = .reject r ↔
      decode doc = .ok r ∧ checkTable r.params r.bound r.rows = false :=
  respond_reject_iff _ _ r

theorem serveAst_refuse_iff (doc : Json) (e : String) :
    serveAst doc = .refuse e ↔ decode doc = .error e :=
  respond_refuse_iff _ _ e

theorem render_take {ρ : Type} (outcome : Response ρ) (detail : Json) :
    (render outcome detail).toList.take 7 = (outcome.word ++ " ").toList := by
  cases outcome <;> simp [render, Response.word, String.toList_append]

theorem serveWith_accept_iff {ρ : Type} (handler : Json → Response ρ)
    (detail : Json → Response ρ → Json) (line : String) :
    (serveWith handler detail line).toList.take 7 = "ACCEPT ".toList ↔
      ∃ doc r, Json.parse line = .ok doc ∧ handler doc = .accept r := by
  unfold serveWith
  cases hparse : Json.parse line with
  | error e => simp [render_take, Response.word]
  | ok doc =>
    cases hout : handler doc <;> simp [render_take, Response.word, hout]

theorem serveWith_reject_iff {ρ : Type} (handler : Json → Response ρ)
    (detail : Json → Response ρ → Json) (line : String) :
    (serveWith handler detail line).toList.take 7 = "REJECT ".toList ↔
      ∃ doc r, Json.parse line = .ok doc ∧ handler doc = .reject r := by
  unfold serveWith
  cases hparse : Json.parse line with
  | error e => simp [render_take, Response.word]
  | ok doc =>
    cases hout : handler doc <;> simp [render_take, Response.word, hout]

theorem serveWith_refuse_iff {ρ : Type} (handler : Json → Response ρ)
    (detail : Json → Response ρ → Json) (line : String) :
    (serveWith handler detail line).toList.take 7 = "REFUSE ".toList ↔
      (∃ e, Json.parse line = .error e) ∨
      ∃ doc e, Json.parse line = .ok doc ∧ handler doc = .refuse e := by
  unfold serveWith
  cases hparse : Json.parse line with
  | error e => simp [render_take, Response.word]
  | ok doc =>
    cases hout : handler doc <;> simp [render_take, Response.word, hout]

theorem serveWith_word_trichotomy {ρ : Type} (handler : Json → Response ρ)
    (detail : Json → Response ρ → Json) (line : String) :
    ((serveWith handler detail line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serveWith handler detail line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serveWith handler detail line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serveWith handler detail line).toList.take 7 = "ACCEPT ".toList ∧
      (serveWith handler detail line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serveWith handler detail line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serveWith handler detail line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serveWith handler detail line).toList.take 7 = "REJECT ".toList ∧
      (serveWith handler detail line).toList.take 7 = "REFUSE ".toList) := by
  unfold serveWith
  cases hparse : Json.parse line with
  | error e => simp [render_take, Response.word]
  | ok doc =>
    cases hout : handler doc <;> simp [render_take, Response.word, hout]

theorem serve_accept_iff (pin line : String) :
    (serve pin line).toList.take 7 = "ACCEPT ".toList ↔
      ∃ doc r, Json.parse line = .ok doc ∧ serveAst doc = .accept r :=
  serveWith_accept_iff _ _ line

theorem serve_reject_iff (pin line : String) :
    (serve pin line).toList.take 7 = "REJECT ".toList ↔
      ∃ doc r, Json.parse line = .ok doc ∧ serveAst doc = .reject r :=
  serveWith_reject_iff _ _ line

theorem serve_refuse_iff (pin line : String) :
    (serve pin line).toList.take 7 = "REFUSE ".toList ↔
      (∃ e, Json.parse line = .error e) ∨
      ∃ doc e, Json.parse line = .ok doc ∧ decode doc = .error e := by
  rw [serve, serveWith_refuse_iff]
  simp only [serveAst_refuse_iff]

theorem serve_word_trichotomy (pin line : String) :
    ((serve pin line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serve pin line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serve pin line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serve pin line).toList.take 7 = "ACCEPT ".toList ∧
      (serve pin line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serve pin line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serve pin line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serve pin line).toList.take 7 = "REJECT ".toList ∧
      (serve pin line).toList.take 7 = "REFUSE ".toList) :=
  serveWith_word_trichotomy _ _ line

theorem serveAst_accept_sound (doc : Json) (r : Request) (h : serveAst doc = .accept r) :
    decode doc = .ok r ∧ r.bound ≤ 65535 ∧ IsQTable r.params r.rows := by
  obtain ⟨hd, hc⟩ := (serveAst_accept_iff doc r).mp h
  exact ⟨hd, ((decode_eq_ok_iff doc r).mp hd).2.2.1, checkTable_sound hc⟩

theorem serve_accept_sound (pin line : String)
    (h : (serve pin line).toList.take 7 = "ACCEPT ".toList) :
    ∃ (doc : Json) (r : Request),
      Json.parse line = .ok doc ∧ decode doc = .ok r ∧ r.bound ≤ 65535 ∧
      IsQTable r.params r.rows := by
  obtain ⟨doc, r, hparse, haccept⟩ := (serve_accept_iff pin line).mp h
  exact ⟨doc, r, hparse, serveAst_accept_sound doc r haccept⟩

theorem serve_accept_domain (pin line : String)
    (h : (serve pin line).toList.take 7 = "ACCEPT ".toList) :
    ∃ (doc : Json) (r : Request),
      Json.parse line = .ok doc ∧ decode doc = .ok r ∧ r.params.valid = true ∧
      r.rows.size = (closure r.bound).size ∧
      (r.rows.toList.map fun entry => entry.1.key).Nodup := by
  obtain ⟨doc, r, hparse, haccept⟩ := (serve_accept_iff pin line).mp h
  obtain ⟨hd, hc⟩ := (serveAst_accept_iff doc r).mp haccept
  obtain ⟨_, _, hvalid, hsize, _⟩ := checkTable_true_iff.mp hc
  exact ⟨doc, r, hparse, hd, hvalid, hsize, checkTable_nodup hc⟩

private theorem encodeRequest_getObjVal {p : Params} {n : Nat}
    {rows : Array (Config × Rat)} {name : String} {value : Json}
    (hmem : (name, value) ∈ CheckerWire.requestFields p n rows) :
    (CheckerWire.encodeRequest p n rows).getObjVal? name = .ok value := by
  have hd : (CheckerWire.requestFields p n rows).Pairwise
      (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [CheckerWire.requestFields, ParamsWire.fields]
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList (CheckerWire.requestFields p n rows) compare).get? name =
    some value at hl
  change (match (Std.TreeMap.Raw.ofList (CheckerWire.requestFields p n rows) compare).get? name
    with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

theorem decode_encodeRequest (p : Params) (hp : p.valid = true) (n : Nat) (hn : n ≤ 65535)
    (rows : Array (Config × Rat)) (hrows : ∀ row ∈ rows, CheckerWire.BoundedConfig row.1) :
    decode (CheckerWire.encodeRequest p n rows) = .ok ⟨p, n, rows⟩ := by
  have hop := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [CheckerWire.requestFields] :
      ("op", toJson "check_table") ∈ CheckerWire.requestFields p n rows)
  have hbound := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [CheckerWire.requestFields] :
      ("n", toJson n) ∈ CheckerWire.requestFields p n rows)
  have hentries := encodeRequest_getObjVal (p := p) (n := n) (rows := rows)
    (by simp [CheckerWire.requestFields] :
      ("entries", .arr (rows.map CheckerWire.encodeEntry)) ∈
        CheckerWire.requestFields p n rows)
  have haop : (CheckerWire.encodeRequest p n rows).getObjValAs? String "op" =
      .ok "check_table" := by
    change Json.getStr?
      (((CheckerWire.encodeRequest p n rows).getObjVal? "op").toOption.getD .null) = _
    rw [hop]
    rfl
  have habound : (CheckerWire.encodeRequest p n rows).getObjValAs? Nat "n" = .ok n := by
    change Json.getNat?
      (((CheckerWire.encodeRequest p n rows).getObjVal? "n").toOption.getD .null) = _
    rw [hbound]
    rfl
  refine (decode_eq_ok_iff _ _).mpr
    ⟨haop, habound, hn, CheckerWire.decode_request_parameters p n rows, hp, ?_⟩
  rw [hentries]
  exact CheckerWire.entries_encode rows hrows

theorem serveAst_exactRestriction (p : Params) (hp : p.valid = true) (n : Nat)
    (hn : n ≤ 65535) :
    serveAst (CheckerWire.encodeRequest p n (CheckerWire.exactRestriction p hp n)) =
      .accept ⟨p, n, CheckerWire.exactRestriction p hp n⟩ :=
  (serveAst_accept_iff _ _).mpr
    ⟨decode_encodeRequest p hp n hn _ (CheckerWire.exactRestriction_bounded p hp n hn),
      CheckerWire.exactRestriction_accepted p hp n⟩

theorem serve_complete (pin line : String) (p : Params) (hp : p.valid = true) (n : Nat)
    (hn : n ≤ 65535)
    (hline : Json.parse line =
      .ok (CheckerWire.encodeRequest p n (CheckerWire.exactRestriction p hp n))) :
    (serve pin line).toList.take 7 = "ACCEPT ".toList :=
  (serve_accept_iff pin line).mpr ⟨_, _, hline, serveAst_exactRestriction p hp n hn⟩

theorem serve_reject_or_refuse_of_wrong (pin line : String)
    (hwrong : ∀ doc r, Json.parse line = .ok doc → decode doc = .ok r →
      ¬ IsQTable r.params r.rows) :
    ¬ (serve pin line).toList.take 7 = "ACCEPT ".toList := by
  intro h
  obtain ⟨doc, r, hparse, hdecode, _, hq⟩ := serve_accept_sound pin line h
  exact hwrong doc r hparse hdecode hq

end Rhone.Computation.CheckedTable
