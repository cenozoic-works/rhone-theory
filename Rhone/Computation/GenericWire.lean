/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.GenericRows
public import Mathlib.Data.Fintype.BigOperators
public import Rhone.Computation.ParamsWireAcceptanceProof
public import Rhone.Computation.ConfigProof
public import Rhone.Computation.QProbabilityProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
/-! # General-allele exact table request reader -/

@[expose] public section
namespace Rhone.Computation.GenericWire
open Lean

def toSpec (ka kb : Nat) (x : Rhone.Computation.Config) :
    Rhone.LinearAlgebra.Recursion.Config ka kb :=
  ⟨fun i => x.a.getD i.val 0, fun j => x.b.getD j.val 0,
    fun i j => x.c.getD (i.val * kb + j.val) 0⟩

def pi (xs : Array Rat) (i : Fin xs.size) : Rat := xs.getD i.val 0

def valid (p : Params) : Bool := decide (
  0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho ∧
  0 < p.piA.size ∧ p.piA.size ≤ 255 ∧ 0 < p.piB.size ∧ p.piB.size ≤ 255 ∧
  (∀ i, 0 < pi p.piA i) ∧ (∀ j, 0 < pi p.piB j) ∧
  (∑ i, pi p.piA i) = 1 ∧ (∑ j, pi p.piB j) = 1)

structure Request where
  params : Params
  bound : Nat
  rawRows : Array (Rhone.Computation.Config × Rat)

def Request.rows (r : Request) :
    List (Rhone.LinearAlgebra.Recursion.Config r.params.piA.size r.params.piB.size × Rat) :=
  r.rawRows.toList.map (fun row =>
    (toSpec r.params.piA.size r.params.piB.size row.1, row.2))

def Request.accepted (r : Request) : Bool :=
  (valid r.params && r.rawRows.all (fun row =>
    row.1.a.size == r.params.piA.size && row.1.b.size == r.params.piB.size &&
      row.1.c.size == r.params.piA.size * r.params.piB.size)) &&
    GenericRows.check r.params.thetaA r.params.thetaB r.params.rho
    (pi r.params.piA) (pi r.params.piB) r.bound r.rows

def fieldsAllowed (doc : Json) (allowed : List String) : Except String Unit := do
  let fields ← doc.getObj?
  if fields.toList.all (fun field => allowed.contains field.1) then return ()
  else throw "unsupported general-table field"

def entry (ka kb : Nat) (doc : Json) : Except String (Rhone.Computation.Config × Rat) := do
  fieldsAllowed doc ["key", "value"]
  let key ← doc.getObjValAs? String "key"
  let value ← doc.getObjValAs? String "value" >>= RationalWire.decode
  let config ← parseConfig key ka kb
  return (config, value)

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "n", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
    "entries", "rhone_version", "provenance"]
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table_general" then throw "unsupported operation"
  let bound ← doc.getObjValAs? Nat "n"
  if bound > 65535 then throw "unsupported bound: exceeds the u16 configuration wire domain"
  let params ← ParamsWire.decode doc
  if !valid params then throw "invalid parameter domain"
  let rows ← (doc.getObjVal? "entries" >>= Json.getArr?) >>= fun rows =>
    rows.mapM (entry params.piA.size params.piB.size)
  return ⟨params, bound, rows⟩

lemma Request.accepted_sound (r : Request) (h : r.accepted = true) :
    ∃ (hA : 0 < r.params.thetaA) (hB : 0 < r.params.thetaB) (hR : 0 ≤ r.params.rho),
      ∀ row ∈ r.rawRows.toList, row.2 =
        Rhone.LinearAlgebra.Recursion.q (πA := pi r.params.piA) (πB := pi r.params.piB)
          hA hB hR (toSpec r.params.piA.size r.params.piB.size row.1) := by
  simp only [Request.accepted, Bool.and_eq_true] at h
  obtain ⟨hA, hB, hR, _, hall⟩ := GenericRows.check_sound h.2
  refine ⟨hA, hB, hR, ?_⟩
  intro row hr
  exact hall _ (List.mem_map.mpr ⟨row, hr, rfl⟩)

def checkRequest (doc : Json) : Except String Bool := do
  let r ← decode doc
  return r.accepted

def request (line : String) : Except String Bool := Json.parse line >>= checkRequest

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl
@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl
@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl
@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α}
    {f : α → Except String β} {b : β} {P : Prop}
    (h : (x >>= f) = .ok b) (k : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases hx : x with
  | error e => simp [hx] at h
  | ok a => exact k a hx (by simpa [hx] using h)

lemma checkRequest_ok (doc : Json) (b : Bool) (h : checkRequest doc = .ok b) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = b := by
  unfold checkRequest at h
  refine of_bind_ok h fun r hr h => ?_
  exact ⟨r, hr, Except.ok.inj h⟩

lemma decode_supplied_fields (doc : Json) (r : Request) (h : decode doc = .ok r) :
    doc.getObjValAs? String "op" = .ok "check_table_general" ∧
    doc.getObjValAs? Nat "n" = .ok r.bound ∧ r.bound ≤ 65535 ∧
    ParamsWire.decode doc = .ok r.params ∧ valid r.params = true ∧
    ∃ js : Array Json, (doc.getObjVal? "entries" >>= Json.getArr?) = .ok js ∧
      js.mapM (entry r.params.piA.size r.params.piB.size) = .ok r.rawRows := by
  unfold decode at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun op hop h => ?_
  by_cases ho : op = "check_table_general"
  · simp only [ho, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine of_bind_ok h fun bound hn h => ?_
    by_cases hb : bound > 65535
    · simp [hb] at h
    · simp only [hb, ↓reduceIte] at h
      refine of_bind_ok h fun p hp h => ?_
      cases hv : valid p with
      | false => simp [hv] at h
      | true =>
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        refine of_bind_ok h fun rows hrows h => ?_
        obtain rfl := Except.ok.inj h
        refine ⟨ho ▸ hop, hn, Nat.le_of_not_gt hb, hp, hv, ?_⟩
        refine of_bind_ok hrows fun js hjs hm => ?_
        exact ⟨js, hjs, hm⟩
  · simp [ho] at h

lemma checkRequest_accepts_original_rows (doc : Json) (h : checkRequest doc = .ok true) :
    ∃ r : Request, decode doc = .ok r ∧
      ∃ (hA : 0 < r.params.thetaA) (hB : 0 < r.params.thetaB) (hR : 0 ≤ r.params.rho),
        ∀ row ∈ r.rawRows.toList, row.2 =
          Rhone.LinearAlgebra.Recursion.q (πA := pi r.params.piA) (πB := pi r.params.piB)
            hA hB hR (toSpec r.params.piA.size r.params.piB.size row.1) := by
  obtain ⟨r, hr, ha⟩ := checkRequest_ok _ _ h
  exact ⟨r, hr, Request.accepted_sound r ha⟩

lemma entry_supplied_fields (ka kb : Nat) (doc : Json)
    (row : Rhone.Computation.Config × Rat) (h : entry ka kb doc = .ok row) :
    ∃ key, doc.getObjValAs? String "key" = .ok key ∧
      (doc.getObjValAs? String "value" >>= RationalWire.decode) = .ok row.2 ∧
      parseConfig key ka kb = .ok row.1 ∧ row.1.key = key := by
  unfold entry at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun key hkey h => ?_
  refine of_bind_ok h fun v hv h => ?_
  refine of_bind_ok h fun config hc h => ?_
  obtain rfl := Except.ok.inj h
  exact ⟨key, hkey, hv, hc, key_eq_of_parseConfig_eq_ok hc⟩

lemma Request.accepted_probability (r : Request) (h : r.accepted = true) :
    ∀ row ∈ r.rawRows.toList, (row.2 : Real) =
      Rhone.Coalescent.TwoLocusGenealogy.qProb (r.params.thetaA : Real) (r.params.thetaB : Real)
        (r.params.rho : Real) (fun i => (pi r.params.piA i : Real))
        (fun j => (pi r.params.piB j : Real))
        (toSpec r.params.piA.size r.params.piB.size row.1) := by
  have hh := h
  simp only [Request.accepted, Bool.and_eq_true, valid, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨_, _, _, _, _, _, _, hpa, hpb, hsa, hsb⟩, _⟩, _⟩ := hh
  obtain ⟨hA, hB, hR, hall⟩ := Request.accepted_sound r h
  intro row hr
  rw [hall row hr]
  exact QProbability.rat_q_probability _ _ _ _ _ hA hB hR
    (fun i => (hpa i).le) hsa (fun j => (hpb j).le) hsb _

lemma request_accept (line : String) (h : request line = .ok true) :
    ∃ doc : Json, Json.parse line = .ok doc ∧
      ∃ r : Request, decode doc = .ok r ∧ r.accepted = true := by
  unfold request at h
  refine of_bind_ok h fun doc hd h => ?_
  exact ⟨doc, hd, checkRequest_ok _ _ h⟩

def entryFields (row : Rhone.Computation.Config × Rat) : List (String × Json) :=
  [("key", .str row.1.key), ("value", .str (RationalWire.strictPrint row.2))]

def encodeEntry (row : Rhone.Computation.Config × Rat) : Json := Json.mkObj (entryFields row)

def requestFields (r : Request) : List (String × Json) :=
  [("op", .str "check_table_general"), ("n", toJson r.bound)] ++
    ParamsWire.fields r.params ++ [("entries", .arr (r.rawRows.map encodeEntry))]

def encode (r : Request) : Json := Json.mkObj (requestFields r)

private theorem encodeEntry_getObjVal {row : Rhone.Computation.Config × Rat}
    {name : String} {value : Json} (hmem : (name, value) ∈ entryFields row) :
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

private theorem fieldsAllowed_mkObj (fields : List (String × Json)) (allowed : List String)
    (h : ∀ p ∈ fields, p.1 ∈ allowed) :
    fieldsAllowed (Json.mkObj fields) allowed = .ok () := by
  have ha : (Std.TreeMap.Raw.ofList fields compare).toList.all
      (fun p => allowed.contains p.1) = true := by
    apply List.all_eq_true.mpr
    intro p hp
    have hget := (Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some
      Std.TreeMap.Raw.WF.ofList).mp hp
    have hm : p.1 ∈ Std.TreeMap.Raw.ofList fields compare :=
      (Std.TreeMap.Raw.mem_iff_isSome_getElem? Std.TreeMap.Raw.WF.ofList).mpr
        (by rw [hget]; rfl)
    have hk := List.contains_iff_mem.mp (Std.TreeMap.Raw.mem_ofList.mp hm)
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hk
    apply List.contains_iff_mem.mpr
    rw [← heq]
    exact h q hq
  unfold fieldsAllowed
  change (if (Std.TreeMap.Raw.ofList fields compare).toList.all
    (fun p => allowed.contains p.1) then Except.ok ()
    else Except.error "unsupported general-table field") = Except.ok ()
  rw [ha]
  rfl

lemma entry_encode (row : Rhone.Computation.Config × Rat) (ka kb : Nat)
    (hka : 1 ≤ ka) (hkb : 1 ≤ kb) (hka255 : ka ≤ 255) (hkb255 : kb ≤ 255)
    (ha : row.1.a.size = ka) (hb : row.1.b.size = kb) (hc : row.1.c.size = ka * kb)
    (hu : ∀ n ∈ row.1.a.toList ++ row.1.b.toList ++ row.1.c.toList, n ≤ 65535) :
    entry ka kb (encodeEntry row) = .ok row := by
  have hkey := encodeEntry_getObjVal (row := row)
    (by simp [entryFields] : ("key", Json.str row.1.key) ∈ entryFields row)
  have hv := encodeEntry_getObjVal (row := row)
    (by simp [entryFields] :
      ("value", Json.str (RationalWire.strictPrint row.2)) ∈ entryFields row)
  have hp := parseConfig_key row.1 ka kb hka hkb hka255 hkb255 ha hb hc hu
  unfold entry
  have hf : fieldsAllowed (encodeEntry row) ["key", "value"] = .ok () := by
    apply fieldsAllowed_mkObj
    simp [entryFields]
  rw [hf]
  simp only [ok_bind]
  have hkey' : (encodeEntry row).getObjValAs? String "key" = .ok row.1.key := by
    change Json.getStr? (((encodeEntry row).getObjVal? "key").toOption.getD .null) = _
    rw [hkey]
    rfl
  have hv' : (encodeEntry row).getObjValAs? String "value" =
      .ok (RationalWire.strictPrint row.2) := by
    change Json.getStr? (((encodeEntry row).getObjVal? "value").toOption.getD .null) = _
    rw [hv]
    rfl
  rw [hkey', hv']
  simp only [ok_bind, RationalWire.decode_strictPrint, hp, pure_def]

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value := by
  have hd : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields, ParamsWire.fields]
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList (requestFields r) compare).get? name = some value at hl
  change (match (Std.TreeMap.Raw.ofList (requestFields r) compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

private theorem encode_parameter_getters (r : Request) {name : String} {value : Json}
    (hmem : (name, value) ∈ ParamsWire.fields r.params) :
    (encode r).getObjVal? name = (ParamsWire.encode r.params).getObjVal? name := by
  rw [encode_getObjVal (value := value) (by simp [requestFields, hmem]),
    ParamsWire.encode_getObjVal hmem]

theorem decode_parameters_encode (r : Request) : ParamsWire.decode (encode r) = .ok r.params := by
  have hθA := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("theta_a", Json.str (RationalWire.strictPrint r.params.thetaA)) ∈ ParamsWire.fields r.params)
  have hθB := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("theta_b", Json.str (RationalWire.strictPrint r.params.thetaB)) ∈ ParamsWire.fields r.params)
  have hρ := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("rho", Json.str (RationalWire.strictPrint r.params.rho)) ∈ ParamsWire.fields r.params)
  have hπA := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("pi_a", Json.arr (r.params.piA.map fun q => Json.str (RationalWire.strictPrint q))) ∈
        ParamsWire.fields r.params)
  have hπB := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("pi_b", Json.arr (r.params.piB.map fun q => Json.str (RationalWire.strictPrint q))) ∈
        ParamsWire.fields r.params)
  rw [ParamsWire.decode_congr hθA hθB hρ hπA hπB, ParamsWire.decode_encode]

def BoundedConfig (ka kb : Nat) (x : Rhone.Computation.Config) : Prop :=
  x.a.size = ka ∧ x.b.size = kb ∧ x.c.size = ka * kb ∧
    ∀ n ∈ x.a.toList ++ x.b.toList ++ x.c.toList, n ≤ 65535

private lemma list_entries_encode (ka kb : Nat) (rows : List (Rhone.Computation.Config × Rat))
    (hka : 1 ≤ ka) (hkb : 1 ≤ kb) (hka255 : ka ≤ 255) (hkb255 : kb ≤ 255)
    (hrows : ∀ row ∈ rows, BoundedConfig ka kb row.1) :
    (rows.map encodeEntry).mapM (entry ka kb) = .ok rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨ha, hb, hc, hu⟩ := hrows row (by simp)
    have hr := entry_encode row ka kb hka hkb hka255 hkb255 ha hb hc hu
    have hs := ih (fun value hv => hrows value (by simp [hv]))
    simp [List.mapM_cons, hr, hs]

lemma entries_encode (ka kb : Nat) (rows : Array (Rhone.Computation.Config × Rat))
    (hka : 1 ≤ ka) (hkb : 1 ≤ kb) (hka255 : ka ≤ 255) (hkb255 : kb ≤ 255)
    (hrows : ∀ row ∈ rows, BoundedConfig ka kb row.1) :
    (rows.map encodeEntry).mapM (entry ka kb) = .ok rows := by
  have hl := list_entries_encode ka kb rows.toList hka hkb hka255 hkb255
    (by simpa using hrows)
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

lemma decode_encode (r : Request) (hv : valid r.params = true) (hn : r.bound ≤ 65535)
    (hrows : ∀ row ∈ r.rawRows,
      BoundedConfig r.params.piA.size r.params.piB.size row.1) :
    decode (encode r) = .ok r := by
  have hvalid := hv
  simp only [valid, decide_eq_true_eq] at hvalid
  obtain ⟨_, _, _, hka, hka255, hkb, hkb255, _, _, _, _⟩ := hvalid
  have hentries := entries_encode _ _ r.rawRows hka hkb hka255 hkb255 hrows
  rw [Array.mapM_map] at hentries
  have hop := encode_getObjVal (r := r)
    (by simp [requestFields] : ("op", Json.str "check_table_general") ∈ requestFields r)
  have hnfield := encode_getObjVal (r := r)
    (by simp [requestFields] : ("n", toJson r.bound) ∈ requestFields r)
  have hf := encode_getObjVal (r := r)
    (by simp [requestFields] :
      ("entries", Json.arr (r.rawRows.map encodeEntry)) ∈ requestFields r)
  have ho : (encode r).getObjValAs? String "op" = .ok "check_table_general" := by
    change Json.getStr? (((encode r).getObjVal? "op").toOption.getD .null) = _
    rw [hop]
    rfl
  have hb : (encode r).getObjValAs? Nat "n" = .ok r.bound := by
    change Json.getNat? (((encode r).getObjVal? "n").toOption.getD .null) = _
    rw [hnfield]
    rfl
  have hfields : fieldsAllowed (encode r)
      ["op", "n", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
        "entries", "rhone_version", "provenance"] = .ok () := by
    apply fieldsAllowed_mkObj
    simp [requestFields, ParamsWire.fields]
  simp [decode, hfields, ho, hb, Nat.not_lt.mpr hn, decode_parameters_encode,
    hv, hf, Json.getArr?, hentries]

def fromSpec {ka kb : Nat} (x : Rhone.LinearAlgebra.Recursion.Config ka kb) :
    Rhone.Computation.Config :=
  ⟨Array.ofFn x.a, Array.ofFn x.b,
    Array.ofFn (fun k : Fin (ka * kb) =>
      x.c (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)⟩

lemma fromSpec_toSpec (ka kb : Nat) (x : Rhone.Computation.Config)
    (ha : x.a.size = ka) (hb : x.b.size = kb) (hc : x.c.size = ka * kb) :
    fromSpec (toSpec ka kb x) = x := by
  have ha' : (fromSpec (toSpec ka kb x)).a = x.a := by
    apply Array.ext (by simpa [fromSpec] using ha.symm)
    intro i hi hxi
    simp [fromSpec, toSpec, Array.getD, hxi]
  have hb' : (fromSpec (toSpec ka kb x)).b = x.b := by
    apply Array.ext (by simpa [fromSpec] using hb.symm)
    intro i hi hxi
    simp [fromSpec, toSpec, Array.getD, hxi]
  have hc' : (fromSpec (toSpec ka kb x)).c = x.c := by
    apply Array.ext (by simpa [fromSpec] using hc.symm)
    intro k hk hxk
    simp [fromSpec, toSpec, Array.getD, Nat.div_add_mod', hxk]
  cases hx : fromSpec (toSpec ka kb x) with
  | mk a b c =>
    cases x with
    | mk d e f =>
      simp only [hx, Rhone.Computation.Config.mk.injEq] at ha' hb' hc' ⊢
      exact ⟨ha', hb', hc'⟩

lemma Request.accepted_arrays (r : Request) (h : r.accepted = true) :
    ∀ row ∈ r.rawRows, fromSpec
      (toSpec r.params.piA.size r.params.piB.size row.1) = row.1 := by
  simp only [Request.accepted, Bool.and_eq_true] at h
  have hs := h.1.2
  simp only [Array.all_eq_true', Bool.and_eq_true, beq_iff_eq] at hs
  intro row hr
  obtain ⟨⟨ha, hb⟩, hc⟩ := hs row hr
  exact fromSpec_toSpec _ _ _ ha hb hc

lemma fieldsAllowed_ok_iff (value : Json) (allowed : List String) :
    fieldsAllowed value allowed = .ok () ↔
      ∃ fields, value.getObj? = .ok fields ∧ ∀ p ∈ fields.toList, p.1 ∈ allowed := by
  cases hobj : value.getObj? with
  | error message => simp [fieldsAllowed, hobj]
  | ok fields => simp [fieldsAllowed, hobj]

lemma decode_fields_allowed (doc : Json) (r : Request) (h : decode doc = .ok r) :
    fieldsAllowed doc ["op", "n", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
      "entries", "rhone_version", "provenance"] = .ok () := by
  unfold decode at h
  refine of_bind_ok h fun guardResult hf _ => ?_
  cases guardResult
  exact hf

lemma entry_fields_allowed (ka kb : Nat) (doc : Json) (row : Rhone.Computation.Config × Rat)
    (h : entry ka kb doc = .ok row) : fieldsAllowed doc ["key", "value"] = .ok () := by
  unfold entry at h
  refine of_bind_ok h fun guardResult hf _ => ?_
  cases guardResult
  exact hf

end Rhone.Computation.GenericWire
