/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.IslandPairRates
public import Rhone.Computation.IslandPairWireProof
public import Rhone.Coalescent.IslandPairLumping
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas

/-! # The island-pair reader that compares the four rate fields -/

@[expose] public section
namespace Rhone.Computation.IslandPairRates
open Lean IslandPairWire

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

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

theorem destinationRate_cast (d : Nat) (m : Rat) :
    (destinationRate d m : Real) = Rhone.Coalescent.IslandPair.destinationRate d (m : Real) := by
  simp [destinationRate, Rhone.Coalescent.IslandPair.destinationRate]

theorem rateValues_cast (d : Nat) (m c : Rat) :
    ((rateValues d m c).getD 0 0 : Real) =
      Rhone.Coalescent.IslandPair.destinationRate d (m : Real) ∧
    ((rateValues d m c).getD 1 0 : Real) =
      Rhone.Coalescent.IslandPair.projectedGenerator d (m : Real) (c : Real) (some true) none ∧
    ((rateValues d m c).getD 2 0 : Real) =
      Rhone.Coalescent.IslandPair.projectedGenerator d (m : Real) (c : Real) (some true)
        (some false) ∧
    ((rateValues d m c).getD 3 0 : Real) =
      Rhone.Coalescent.IslandPair.projectedGenerator d (m : Real) (c : Real) (some false)
        (some true) := by
  have e0 : (rateValues d m c).getD 0 0 = destinationRate d m := rfl
  have e1 : (rateValues d m c).getD 1 0 = c := rfl
  have e2 : (rateValues d m c).getD 2 0 = 2 * m := rfl
  have e3 : (rateValues d m c).getD 3 0 = 2 * destinationRate d m := rfl
  rw [e0, e1, e2, e3]
  refine ⟨destinationRate_cast d m, rfl, ?_, ?_⟩
  · simp [Rhone.Coalescent.IslandPair.projectedGenerator]
  · simp [Rhone.Coalescent.IslandPair.projectedGenerator, destinationRate_cast]

theorem destinationRate_eventRate (d : Nat) (m c : Rat) (a b x : Fin d) (hax : a ≠ x) :
    (destinationRate d m : Real) =
      Rhone.Coalescent.IslandPair.eventRate d (m : Real) (c : Real) (some (a, b))
        (some (x, b)) := by
  simp [Rhone.Coalescent.IslandPair.eventRate, hax, destinationRate_cast]

theorem checkRates_iff (d : Nat) (m c : Rat) (claim : Array Rat) :
    checkRates d m c claim = true ↔ claim = rateValues d m c := by
  simp [checkRates]

theorem Request.check_iff (r : Request) :
    r.check = true ↔
      r.report.claim = IslandPair.values r.report.demes r.report.migration
        r.report.coalescence ∧
      r.rates = rateValues r.report.demes r.report.migration r.report.coalescence := by
  simp [Request.check, IslandPair.check_iff, checkRates_iff]

theorem Request.count_eq (r : Request) : r.count = 7 := rfl

private theorem stamp_fields (d : Bool × Nat) :
    ([("schema", toJson "rhone-compute-island-pair-rates-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have ha : ∀ d : Bool × Nat, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hc : ∀ d : Bool × Nat,
      (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2 :=
    fun d => getNat_of (mkObj_getObjVal (stamp_fields d) (by simp))
  have h1 := ha first
  have h2 := hc first
  rw [h] at h1 h2
  rw [ha second] at h1
  rw [hc second] at h2
  cases first
  cases second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2
  simp [h1, h2]

theorem stamp_ne_wire_stamp (d e : Bool × Nat) : stamp d ≠ IslandPairWire.stamp e := by
  intro h
  have h1 : (stamp d).getObjVal? "schema" =
      .ok (.str "rhone-compute-island-pair-rates-check-v1") :=
    mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hfields : ([("schema", toJson "rhone-compute-island-pair-check-v1"),
      ("accepted", toJson e.1), ("checked_rational_values", toJson e.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp
  have h2 : (IslandPairWire.stamp e).getObjVal? "schema" =
      .ok (.str "rhone-compute-island-pair-check-v1") :=
    mkObj_getObjVal hfields (by simp [toJson])
  rw [h, h2] at h1
  simp at h1

theorem decode_report (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    IslandPairWire.decode doc = .ok r.report := by
  unfold decode at hdecode
  cases hreport : IslandPairWire.decode doc with
  | error message => simp [hreport] at hdecode
  | ok report =>
    rw [hreport] at hdecode
    simp only [ok_bind] at hdecode
    cases h1 : rat doc "per_destination_lineage_migration_rate" with
    | error message => simp [h1] at hdecode
    | ok v1 =>
      cases h2 : rat doc "same_to_coalesced_rate" with
      | error message => simp [h1, h2] at hdecode
      | ok v2 =>
        cases h3 : rat doc "same_to_different_rate" with
        | error message => simp [h1, h2, h3] at hdecode
        | ok v3 =>
          cases h4 : rat doc "different_to_same_rate" with
          | error message => simp [h1, h2, h3, h4] at hdecode
          | ok v4 =>
            simp only [h1, h2, h3, h4, ok_bind, pure_def, Except.ok.injEq] at hdecode
            rw [← hdecode]

private theorem requestFields_pairwise (r : Request) :
    (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp [requestFields, IslandPairWire.requestFields]

private theorem decode_encode_report (r : Request) :
    IslandPairWire.decode (encode r) = .ok r.report := by
  have hd := requestFields_pairwise r
  have hschema := getStr_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields, toJson] :
    ("schema", Json.str "rhone.island_pair.v1") ∈ requestFields r))
  have hsemantics := getStr_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields, toJson] :
    ("comparison_semantics", Json.str "exact_fraction") ∈ requestFields r))
  have hmodel := getStr_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields, toJson] :
    ("model", Json.str "labelled symmetric finite-deme two-lineage coalescent") ∈
      requestFields r))
  have hdemes := getNat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("demes", toJson r.report.demes) ∈ requestFields r))
  have hm := rat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("migration_rate", encodeRat r.report.migration) ∈ requestFields r))
  have hc := rat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("coalescence_rate", encodeRat r.report.coalescence) ∈ requestFields r))
  have hunit := getStr_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("time_unit", Json.str r.report.timeUnit) ∈ requestFields r))
  have hprov := getStr_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("parameter_provenance", Json.str r.report.provenance) ∈ requestFields r))
  have hsame := rat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("same_deme_mean_time", encodeRat r.report.same) ∈ requestFields r))
  have hdiff := rat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("different_deme_mean_time", encodeRat r.report.different) ∈ requestFields r))
  have hcontrast := rat_of (mkObj_getObjVal hd
    (by simp [requestFields, IslandPairWire.requestFields] :
    ("time_contrast", encodeRat r.report.contrast) ∈ requestFields r))
  simp only [encode] at *
  simp [IslandPairWire.decode, hschema, hsemantics, hmodel, hdemes, hm, hc, hunit, hprov,
    hsame, hdiff, hcontrast]

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hd := requestFields_pairwise r
  have h1 := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("per_destination_lineage_migration_rate", encodeRat r.destination) ∈ requestFields r))
  have h2 := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("same_to_coalesced_rate", encodeRat r.sameToCoalesced) ∈ requestFields r))
  have h3 := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("same_to_different_rate", encodeRat r.sameToDifferent) ∈ requestFields r))
  have h4 := rat_of (mkObj_getObjVal hd (by simp [requestFields] :
    ("different_to_same_rate", encodeRat r.differentToSame) ∈ requestFields r))
  have h0 := decode_encode_report r
  simp only [encode] at *
  simp [decode, h0, h1, h2, h3, h4]

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.report.valid = true ∧
      out = stamp (r.check, r.count) := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.report.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      refine ⟨r, rfl, hvalid, ?_⟩
      simpa [hdecode, hvalid, Except.map] using hok.symm

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.report.valid = true ∧
      r.report.claim = IslandPair.values r.report.demes r.report.migration
        r.report.coalescence ∧
      r.rates = rateValues r.report.demes r.report.migration r.report.coalescence ∧
      count = 7 := by
  obtain ⟨r, hdecode, hvalid, hout⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hclaim, hrates⟩ := (Request.check_iff r).mp hpair.1.symm
  exact ⟨r, hdecode, hvalid, hclaim, hrates, hpair.2⟩

theorem decision_wire (doc : Json) (d : Bool × Nat) (h : decision doc = .ok d) :
    ∃ e : Bool × Nat, IslandPairWire.decision doc = .ok e ∧ (d.1 = true → e.1 = true) := by
  unfold decision at h
  cases hdecode : decode doc with
  | error message => simp [hdecode] at h
  | ok r =>
    cases hvalid : r.report.valid with
    | false => simp [hdecode, hvalid] at h
    | true =>
      have hd : d = (r.check, r.count) := by simpa [hdecode, hvalid] using h.symm
      refine ⟨(IslandPair.check r.report.demes r.report.migration r.report.coalescence
        r.report.claim, r.report.claim.size), ?_, ?_⟩
      · simp [IslandPairWire.decision, decode_report doc r hdecode, hvalid]
      · intro hcheck
        rw [hd] at hcheck
        exact (IslandPair.check_iff _ _ _ _).mpr ((Request.check_iff r).mp hcheck).1

theorem requestAst_accept_wire (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    IslandPairWire.requestAst doc = .ok (IslandPairWire.stamp (true, 3)) := by
  obtain ⟨r, hdecode, hvalid, hclaim, -, -⟩ := requestAst_accept_sound doc count haccept
  have hcheck := (IslandPair.check_iff _ _ _ _).mpr hclaim
  have hsize : r.report.claim.size = 3 := rfl
  simp [IslandPairWire.requestAst, IslandPairWire.decision, decode_report doc r hdecode,
    hvalid, hcheck, hsize, Except.map]

theorem requestAst_ofFormula (d : Nat) (m c : Rat) (timeUnit provenance : String)
    (hlower : 2 ≤ d) (hupper : d ≤ 65535) (hm : 0 < m) (hc : 0 < c) (hunit : timeUnit ≠ "")
    (hprov : provenance ≠ "") :
    requestAst (encode (Request.ofFormula d m c timeUnit provenance)) =
      .ok (stamp (true, 7)) := by
  have hvalid : (Request.ofFormula d m c timeUnit provenance).report.valid = true :=
    (Report.valid_iff _).mpr ⟨hlower, hupper, hm, hc, hunit, hprov⟩
  have hcheck : (Request.ofFormula d m c timeUnit provenance).check = true :=
    (Request.check_iff _).mpr ⟨rfl, rfl⟩
  simp [requestAst, decision, decode_encode, hvalid, hcheck, Request.count_eq, Except.map]

theorem requestAst_accept_law (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 2 ≤ r.report.demes ∧
      (r.destination : Real) =
        Rhone.Coalescent.IslandPair.destinationRate r.report.demes (r.report.migration : Real) ∧
      (r.sameToCoalesced : Real) = Rhone.Coalescent.IslandPair.projectedGenerator r.report.demes
        (r.report.migration : Real) (r.report.coalescence : Real) (some true) none ∧
      (r.sameToDifferent : Real) = Rhone.Coalescent.IslandPair.projectedGenerator r.report.demes
        (r.report.migration : Real) (r.report.coalescence : Real) (some true) (some false) ∧
      (r.differentToSame : Real) = Rhone.Coalescent.IslandPair.projectedGenerator r.report.demes
        (r.report.migration : Real) (r.report.coalescence : Real) (some false)
        (some true) := by
  obtain ⟨r, hdecode, hvalid, -, hrates, -⟩ := requestAst_accept_sound doc count haccept
  obtain ⟨hlower, -⟩ := (Report.valid_iff r.report).mp hvalid
  obtain ⟨h0, h1, h2, h3⟩ :=
    rateValues_cast r.report.demes r.report.migration r.report.coalescence
  rw [← hrates] at h0 h1 h2 h3
  exact ⟨r, hdecode, hlower, h0, h1, h2, h3⟩

end Rhone.Computation.IslandPairRates
