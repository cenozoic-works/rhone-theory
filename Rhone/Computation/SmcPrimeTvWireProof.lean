/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SmcPrimeTvWire
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the SMC-prime total-variation report reader -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTvWire
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

private theorem mkObj_getObjVal {fields : List (String × Json)} {name : String}
    {value : Json} (hd : fields.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (hmem : (name, value) ∈ fields) :
    (Json.mkObj fields).getObjVal? name = .ok value := by
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList fields compare).get? name = some value at hl
  change (match (Std.TreeMap.Raw.ofList fields compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

private theorem getStr_of {object : Json} {name value : String}
    (h : object.getObjVal? name = .ok (.str value)) :
    object.getObjValAs? String name = .ok value := by
  change Json.getStr? ((object.getObjVal? name).toOption.getD .null) = _
  rw [h]
  rfl

private theorem getNat_of {object : Json} {name : String} {value : Nat}
    (h : object.getObjVal? name = .ok (toJson value)) :
    object.getObjValAs? Nat name = .ok value := by
  change Json.getNat? ((object.getObjVal? name).toOption.getD .null) = _
  rw [h]
  rfl

private theorem getModels_of {object : Json}
    (h : object.getObjVal? "models" = .ok (toJson modelNames)) :
    object.getObjValAs? (Array String) "models" = .ok modelNames := by
  change fromJson? ((object.getObjVal? "models").toOption.getD .null) = _
  rw [h]
  change (fromJson? (toJson modelNames) : Except String (Array String)) = _
  unfold modelNames
  simp [Array.fromJson?, Array.toJson, toJson, fromJson?, Array.mapM_eq_mapM_toList,
    Json.getStr?, List.mapM_cons]

private theorem rat_of {object : Json} {name : String} {value : Rat}
    (h : object.getObjVal? name = .ok (.str (RationalWire.strictPrint value))) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  change parseStrictRat (RationalWire.strictPrint value) = _
  unfold parseStrictRat
  rw [RationalWire.decode_strictPrint]
  simp

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ (1 ≤ r.geneCopies ∧ r.geneCopies ≤ 256 ∧ 0 ≤ r.intensity ∧
      (RationalWire.strictPrint r.intensity).utf8ByteSize ≤ 64) ∧
      boundedNonempty r.windowId 128 = true ∧ boundedNonempty r.provenance 512 = true := by
  simp [Request.valid, and_assoc]

theorem Request.claim_ofFormula (n : Nat) (R : Rat) (w p : String) :
    (Request.ofFormula n R w p).claim = SmcPrimeTv.reportValues n R := rfl

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-smc-prime-tv-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("checker", toJson "Rhone.Computation.SmcPrimeTv.checkReport"),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    intro d
    simp
  have ha : ∀ d : Bool × Nat, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (hd d) (by simp [toJson])
  have hc : ∀ d : Bool × Nat,
      (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2 :=
    fun d => getNat_of (mkObj_getObjVal (hd d) (by simp))
  have h1 := ha first
  have h2 := hc first
  rw [h] at h1 h2
  rw [ha second] at h1
  rw [hc second] at h2
  cases first
  cases second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2
  simp [h1, h2]

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hdq : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hdb : (boundFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [boundFields]
  have hschema := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("schema", Json.str schemaName) ∈ requestFields r))
  have hsemantics := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("comparison_semantics", Json.str "exact_fraction") ∈ requestFields r))
  have hmodels := getModels_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("models", toJson modelNames) ∈ requestFields r))
  have hscope := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("observation_scope", Json.str scopeName) ∈ requestFields r))
  have hn := getNat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("gene_copies", toJson r.geneCopies) ∈ requestFields r))
  have hindex := getNat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("recursion_index", toJson (r.geneCopies - 1)) ∈ requestFields r))
  have hintensity := rat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("integrated_recombination_intensity", Json.str (RationalWire.strictPrint r.intensity))
      ∈ requestFields r))
  have hwindow := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("window_id", Json.str r.windowId) ∈ requestFields r))
  have hprovenance := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("model_provenance", Json.str r.provenance) ∈ requestFields r))
  have hbounds := mkObj_getObjVal hdq (by simp [requestFields] :
    ("bounds", Json.mkObj (boundFields r)) ∈ requestFields r)
  have hsize : (Json.mkObj (boundFields r)).getObj? =
      .ok (Std.TreeMap.Raw.ofList (boundFields r) compare) := rfl
  have hcount : (Std.TreeMap.Raw.ofList (boundFields r) compare).size = 4 := by
    rw [Std.TreeMap.Raw.size_ofList hdb]
    rfl
  have hd1 := mkObj_getObjVal hdb (by simp [boundFields] :
    ("double_bound", Json.str (RationalWire.strictPrint r.doubleBound)) ∈ boundFields r)
  have hd2 := mkObj_getObjVal hdb (by simp [boundFields] :
    ("quadratic_coefficient", Json.str (RationalWire.strictPrint r.coefficient)) ∈
      boundFields r)
  have hd3 := mkObj_getObjVal hdb (by simp [boundFields] :
    ("quadratic_bound", Json.str (RationalWire.strictPrint r.quadratic)) ∈ boundFields r)
  have hd4 := mkObj_getObjVal hdb (by simp [boundFields] :
    ("clipped_quadratic_bound", Json.str (RationalWire.strictPrint r.clipped)) ∈
      boundFields r)
  have hexact : exactBounds (Json.mkObj (boundFields r)) = .ok () := by
    simp [exactBounds, hsize, hcount, hd1, hd2, hd3, hd4]
  have hb1 := rat_of hd1
  have hb2 := rat_of hd2
  have hb3 := rat_of hd3
  have hb4 := rat_of hd4
  simp only [encode] at *
  simp [decode, hschema, hsemantics, hmodels, hscope, hn, hindex, hintensity, hwindow,
    hprovenance, hbounds, hexact, hb1, hb2, hb3, hb4]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then
      .ok (SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim, r.claim.size)
      else .error "request outside the supported domain" := by
  simp [decision, decode_encode]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) =
      .ok (stamp (SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim, r.claim.size)) := by
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (houtside : r.valid = false) :
    requestAst (encode r) = .error "request outside the supported domain" := by
  simp [requestAst, decision_encode, houtside, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim, r.claim.size) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out =
          stamp (SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout, hout ▸ requestAst_encode r hvalid⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      1 ≤ r.geneCopies ∧ 0 ≤ r.intensity ∧
      r.claim = SmcPrimeTv.reportValues r.geneCopies r.intensity ∧ count = r.claim.size ∧
      requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨h1, h2, h3⟩ := (SmcPrimeTv.checkReport_iff _ _ _).mp hpair.1.symm
  exact ⟨r, hdecode, hvalid, h1, h2, h3, hpair.2, hencode⟩

theorem requestAst_encode_accept_sound (r : Request) (count : Nat)
    (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    r.valid = true ∧ r.claim = SmcPrimeTv.reportValues r.geneCopies r.intensity ∧
      count = r.claim.size := by
  obtain ⟨decoded, hdecode, hvalid, -, -, hclaim, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode] at hdecode
  cases hdecode
  exact ⟨hvalid, hclaim, hcount⟩

theorem requestAst_ofFormula (n : Nat) (R : Rat) (w p : String)
    (hvalid : (Request.ofFormula n R w p).valid = true) :
    requestAst (encode (Request.ofFormula n R w p)) =
      .ok (stamp (true, (SmcPrimeTv.reportValues n R).size)) := by
  have h := requestAst_encode (Request.ofFormula n R w p) hvalid
  rw [Request.claim_ofFormula] at h
  rw [h]
  obtain ⟨⟨hn, -, hR, -⟩, -, -⟩ := (Request.valid_iff _).mp hvalid
  change Except.ok (stamp (SmcPrimeTv.checkReport n R (SmcPrimeTv.reportValues n R), _)) = _
  rw [SmcPrimeTv.checkReport_complete n hn R hR]

theorem requestAst_accept_check (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      SmcPrimeTv.checkReport r.geneCopies r.intensity r.claim = true := by
  obtain ⟨r, hdecode, -, h1, h2, hclaim, -, -⟩ := requestAst_accept_sound doc count haccept
  exact ⟨r, hdecode, (SmcPrimeTv.checkReport_iff _ _ _).mpr ⟨h1, h2, hclaim⟩⟩

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.SmcPrimeTvWire
