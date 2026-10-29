/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckedTableProof
public import Rhone.Computation.CorrectnessProof
import all Init.Control.Except

/-! # Meaning of the response line of the recompute-based table check -/

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

theorem checkRows_sound {p : Params} {rows : Array (Config × Rat)}
    (h : checkRows p rows = true) : IsQTable p rows := by
  simp only [checkRows, Bool.and_eq_true] at h
  obtain ⟨hp, hall⟩ := h
  obtain ⟨hθA, hθB, hρ, _⟩ := (Params.valid_iff p).mp hp
  refine ⟨hθA, hθB, hρ, ?_⟩
  intro entry hmem
  have he := Array.all_eq_true'.mp hall entry hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hv⟩ := he
  rw [q_eq_recursion p entry.1 hp ha hb hc hθA hθB hρ] at hv
  exact (by simpa using hv : _ = entry.2).symm

theorem checkRows_complete (p : Params) (hp : p.valid = true) (rows : Array (Config × Rat))
    (hshape : ∀ entry ∈ rows,
      entry.1.a.size = 2 ∧ entry.1.b.size = 2 ∧ entry.1.c.size = 4)
    (hq : IsQTable p rows) : checkRows p rows = true := by
  obtain ⟨hθA, hθB, hρ, hrows⟩ := hq
  simp only [checkRows, hp, Bool.true_and]
  rw [Array.all_eq_true']
  intro entry hmem
  obtain ⟨ha, hb, hc⟩ := hshape entry hmem
  rw [q_eq_recursion p entry.1 hp ha hb hc hθA hθB hρ]
  simpa [ha, hb, hc] using (hrows entry hmem).symm

theorem decodeRows_eq_ok_iff (doc : Json) (r : RowsRequest) :
    decodeRows doc = .ok r ↔
      doc.getObjValAs? String "op" = .ok "check_q_rows" ∧
      ParamsWire.decodeTyped doc = .ok r.params ∧ r.params.valid = true ∧
      (doc.getObjVal? "entries" >>= CheckerWire.entries) = .ok r.rows := by
  rcases r with ⟨p, rows⟩
  cases hop : doc.getObjValAs? String "op" with
  | error e => simp [decodeRows, hop]
  | ok op =>
    by_cases hopv : op = "check_q_rows"
    · cases hp : ParamsWire.decodeTyped doc with
      | error e => simp [decodeRows, hop, hopv, hp]
      | ok q =>
        by_cases hv : q.valid = true
        · cases hr : (doc.getObjVal? "entries" >>= CheckerWire.entries) with
          | error e => simp [decodeRows, hop, hopv, hp, hv, hr]
          | ok rows' =>
            have key : decodeRows doc = .ok ⟨q, rows'⟩ := by
              simp [decodeRows, hop, hopv, hp, hv, hr]
            rw [key]
            constructor
            · intro h
              cases h
              exact ⟨by rw [hopv], rfl, hv, rfl⟩
            · rintro ⟨_, h2, _, h4⟩
              cases h2
              cases h4
              rfl
        · have key : decodeRows doc = .error "invalid parameter domain" := by
            simp [decodeRows, hop, hopv, hp, hv]
          rw [key]
          constructor
          · intro h
            cases h
          · rintro ⟨_, h2, h3, _⟩
            cases h2
            exact absurd h3 hv
    · simp [decodeRows, hop, hopv]

theorem recomputeAst_accept_iff (doc : Json) (r : RowsRequest) :
    recomputeAst doc = .accept r ↔
      decodeRows doc = .ok r ∧ checkRows r.params r.rows = true :=
  respond_accept_iff _ _ r

theorem recomputeAst_reject_iff (doc : Json) (r : RowsRequest) :
    recomputeAst doc = .reject r ↔
      decodeRows doc = .ok r ∧ checkRows r.params r.rows = false :=
  respond_reject_iff _ _ r

theorem recomputeAst_refuse_iff (doc : Json) (e : String) :
    recomputeAst doc = .refuse e ↔ decodeRows doc = .error e :=
  respond_refuse_iff _ _ e

theorem serveRecompute_accept_iff (pin line : String) :
    (serveRecompute pin line).toList.take 7 = "ACCEPT ".toList ↔
      ∃ doc r, Json.parse line = .ok doc ∧ recomputeAst doc = .accept r :=
  serveWith_accept_iff _ _ line

theorem serveRecompute_refuse_iff (pin line : String) :
    (serveRecompute pin line).toList.take 7 = "REFUSE ".toList ↔
      (∃ e, Json.parse line = .error e) ∨
      ∃ doc e, Json.parse line = .ok doc ∧ decodeRows doc = .error e := by
  rw [serveRecompute, serveWith_refuse_iff]
  simp only [recomputeAst_refuse_iff]

theorem serveRecompute_word_trichotomy (pin line : String) :
    ((serveRecompute pin line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serveRecompute pin line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serveRecompute pin line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serveRecompute pin line).toList.take 7 = "ACCEPT ".toList ∧
      (serveRecompute pin line).toList.take 7 = "REJECT ".toList ∧
      ¬ (serveRecompute pin line).toList.take 7 = "REFUSE ".toList) ∨
    (¬ (serveRecompute pin line).toList.take 7 = "ACCEPT ".toList ∧
      ¬ (serveRecompute pin line).toList.take 7 = "REJECT ".toList ∧
      (serveRecompute pin line).toList.take 7 = "REFUSE ".toList) :=
  serveWith_word_trichotomy _ _ line

theorem serveRecompute_accept_sound (pin line : String)
    (h : (serveRecompute pin line).toList.take 7 = "ACCEPT ".toList) :
    ∃ (doc : Json) (r : RowsRequest),
      Json.parse line = .ok doc ∧ decodeRows doc = .ok r ∧ IsQTable r.params r.rows := by
  obtain ⟨doc, r, hparse, haccept⟩ := (serveRecompute_accept_iff pin line).mp h
  obtain ⟨hd, hc⟩ := (recomputeAst_accept_iff doc r).mp haccept
  exact ⟨doc, r, hparse, hd, checkRows_sound hc⟩

end Rhone.Computation.CheckedTable
