/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWire
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Rhone.Computation.ConfigProof
public import Rhone.Computation.ParamsWireProof
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Exact fidelity of finite-checker rows -/

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


def BoundedConfig (c : Config) : Prop :=
  c.a.size = 2 ∧ c.b.size = 2 ∧ c.c.size = 4 ∧
    ∀ n ∈ c.a.toList ++ c.b.toList ++ c.c.toList, n ≤ 65535

private theorem encodeEntry_getObjVal {row : Config × Rat} {name : String} {value : Json}
    (hmem : (name, value) ∈ entryFields row) :
    (encodeEntry row).getObjVal? name = .ok value := by
  have hd : (entryFields row).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [entryFields]
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList (entryFields row) compare).get? name = some value at hl
  change (match (Std.TreeMap.Raw.ofList (entryFields row) compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

theorem entry_encode (row : Config × Rat) (hrow : BoundedConfig row.1) :
    entry (encodeEntry row) = .ok row := by
  obtain ⟨ha, hb, hc, hu⟩ := hrow
  have hk := encodeEntry_getObjVal (row := row) (by simp [entryFields] :
    ("key", Json.str row.1.key) ∈ entryFields row)
  have hv := encodeEntry_getObjVal (row := row) (by simp [entryFields] :
    ("value", Json.str (RationalWire.strictPrint row.2)) ∈ entryFields row)
  have hp := parseConfig_key row.1 2 2 (by decide) (by decide) (by decide) (by decide)
    ha hb (by simpa using hc) hu
  have hka : (encodeEntry row).getObjValAs? String "key" = .ok row.1.key := by
    change Json.getStr? (((encodeEntry row).getObjVal? "key").toOption.getD .null) = _
    rw [hk]
    rfl
  have hva : (encodeEntry row).getObjValAs? String "value" =
      .ok (RationalWire.strictPrint row.2) := by
    change Json.getStr? (((encodeEntry row).getObjVal? "value").toOption.getD .null) = _
    rw [hv]
    rfl
  simp [entry, hka, hva, RationalWire.decode_strictPrint, hp]

private theorem list_entries_encode (rows : List (Config × Rat))
    (hrows : ∀ row ∈ rows, BoundedConfig row.1) :
    (rows.map encodeEntry).mapM entry = .ok rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hr := entry_encode row (hrows row (by simp))
    have hs := ih (fun value hv => hrows value (by simp [hv]))
    simp [List.mapM_cons, hr, hs]

theorem entries_encode (rows : Array (Config × Rat))
    (hrows : ∀ row ∈ rows, BoundedConfig row.1) :
    entries (.arr (rows.map encodeEntry)) = .ok rows := by
  have hl := list_entries_encode rows.toList (by simpa using hrows)
  change (rows.map encodeEntry).mapM entry = .ok rows
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

end Rhone.Computation.CheckerWire
