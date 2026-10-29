/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.IslandPairWire
public import Rhone.Computation.IslandPairAcceptanceProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas

/-! # Fidelity of the island-pair report reader -/

@[expose] public section
namespace Rhone.Computation.IslandPairWire
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

private theorem rat_of {object : Json} {name : String} {value : Rat}
    (h : object.getObjVal? name = .ok (encodeRat value)) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

theorem Report.valid_iff (r : Report) :
    r.valid = true ↔ 2 ≤ r.demes ∧ r.demes ≤ 65535 ∧ 0 < r.migration ∧ 0 < r.coalescence ∧
      r.timeUnit ≠ "" ∧ r.provenance ≠ "" := by
  simp [Report.valid]

theorem Report.claim_ofFormula (d : Nat) (m c : Rat) (timeUnit provenance : String) :
    (Report.ofFormula d m c timeUnit provenance).claim = IslandPair.values d m c := rfl

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-island-pair-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
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

theorem decode_encode (r : Report) : decode (encode r) = .ok r := by
  have hd : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hschema := getStr_of (mkObj_getObjVal hd (by simp [requestFields, toJson] :
    ("schema", Json.str "rhone.island_pair.v1") ∈ requestFields r))
  have hsemantics := getStr_of (mkObj_getObjVal hd (by simp [requestFields, toJson] :
    ("comparison_semantics", Json.str "exact_fraction") ∈ requestFields r))
  have hmodel := getStr_of (mkObj_getObjVal hd (by simp [requestFields, toJson] :
    ("model", Json.str "labelled symmetric finite-deme two-lineage coalescent") ∈
      requestFields r))
  have hdemes := getNat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("demes", toJson r.demes) ∈ requestFields r))
  have hm := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("migration_rate", encodeRat r.migration) ∈ requestFields r))
  have hc := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("coalescence_rate", encodeRat r.coalescence) ∈ requestFields r))
  have hunit := getStr_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("time_unit", Json.str r.timeUnit) ∈ requestFields r))
  have hprov := getStr_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("parameter_provenance", Json.str r.provenance) ∈ requestFields r))
  have hsame := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("same_deme_mean_time", encodeRat r.same) ∈ requestFields r))
  have hdiff := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("different_deme_mean_time", encodeRat r.different) ∈ requestFields r))
  have hcontrast := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("time_contrast", encodeRat r.contrast) ∈ requestFields r))
  simp only [encode] at *
  simp [decode, hschema, hsemantics, hmodel, hdemes, hm, hc, hunit, hprov, hsame, hdiff,
    hcontrast]

private theorem decision_encode (r : Report) :
    decision (encode r) = if r.valid then
      .ok (IslandPair.check r.demes r.migration r.coalescence r.claim, r.claim.size)
      else .error "unsupported island-pair request domain" := by
  simp [decision, decode_encode]

theorem requestAst_encode (r : Report) (hlower : 2 ≤ r.demes) (hupper : r.demes ≤ 65535)
    (hm : 0 < r.migration) (hc : 0 < r.coalescence) (hunit : r.timeUnit ≠ "")
    (hprov : r.provenance ≠ "") :
    requestAst (encode r) =
      .ok (stamp (IslandPair.check r.demes r.migration r.coalescence r.claim, r.claim.size)) := by
  have hvalid : r.valid = true :=
    (Report.valid_iff r).mpr ⟨hlower, hupper, hm, hc, hunit, hprov⟩
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_encode_outside (r : Report)
    (houtside : ¬ (2 ≤ r.demes ∧ r.demes ≤ 65535 ∧ 0 < r.migration ∧ 0 < r.coalescence ∧
      r.timeUnit ≠ "" ∧ r.provenance ≠ "")) :
    requestAst (encode r) = .error "unsupported island-pair request domain" := by
  have hvalid : r.valid = false := by
    cases h : r.valid
    · rfl
    · exact absurd ((Report.valid_iff r).mp h) houtside
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Report, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (IslandPair.check r.demes r.migration r.coalescence r.claim, r.claim.size) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      obtain ⟨hlower, hupper, hm, hc, hunit, hprov⟩ := (Report.valid_iff r).mp hvalid
      have hout : out =
          stamp (IslandPair.check r.demes r.migration r.coalescence r.claim,
            r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout,
        hout ▸ requestAst_encode r hlower hupper hm hc hunit hprov⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Report, decode doc = .ok r ∧ r.valid = true ∧
      r.claim = IslandPair.values r.demes r.migration r.coalescence ∧ count = r.claim.size ∧
      requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  exact ⟨r, hdecode, hvalid, (IslandPair.check_iff _ _ _ _).mp hpair.1.symm, hpair.2,
    hencode⟩

theorem requestAst_encode_accept_sound (r : Report) (count : Nat)
    (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    r.valid = true ∧ r.claim = IslandPair.values r.demes r.migration r.coalescence ∧
      count = r.claim.size := by
  obtain ⟨decoded, hdecode, hvalid, hclaim, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode] at hdecode
  cases hdecode
  exact ⟨hvalid, hclaim, hcount⟩

theorem requestAst_ofFormula (d : Nat) (m c : Rat) (timeUnit provenance : String)
    (hlower : 2 ≤ d) (hupper : d ≤ 65535) (hm : 0 < m) (hc : 0 < c) (hunit : timeUnit ≠ "")
    (hprov : provenance ≠ "") :
    requestAst (encode (Report.ofFormula d m c timeUnit provenance)) =
      .ok (stamp (true, (IslandPair.values d m c).size)) := by
  have h := requestAst_encode (Report.ofFormula d m c timeUnit provenance) hlower hupper hm hc
    hunit hprov
  rw [Report.claim_ofFormula] at h
  rw [h]
  change Except.ok (stamp (IslandPair.check d m c (IslandPair.values d m c), _)) = _
  rw [IslandPair.check_complete]

theorem requestAst_accept_request (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Report, decode doc = .ok r ∧
      (⟨r.demes, r.migration, r.coalescence⟩ : IslandPair.Request).valid = true ∧
      (⟨r.demes, r.migration, r.coalescence⟩ : IslandPair.Request).check r.claim = true := by
  obtain ⟨r, hdecode, hvalid, hclaim, -, -⟩ := requestAst_accept_sound doc count haccept
  obtain ⟨hlower, hupper, hm, hc, -, -⟩ := (Report.valid_iff r).mp hvalid
  exact ⟨r, hdecode, (IslandPair.Request.valid_iff _).mpr ⟨hlower, hupper, hm, hc⟩,
    (IslandPair.check_iff _ _ _ _).mpr hclaim⟩

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.IslandPairWire
