/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PartialSelfingWire
public import Rhone.Computation.PartialSelfingCertificateProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the partial-selfing report reader -/

@[expose] public section
namespace Rhone.Computation.PartialSelfingWire
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
    (h : object.getObjVal? name = .ok (encodeEntry value)) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ 2 ≤ r.labels.size ∧ r.labels.size ≤ 8 ∧
      r.labels.toList.eraseDups.length = r.labels.size ∧ r.generations ≤ 128 ∧
      r.provenance.trimAscii.toString.isEmpty = false ∧
      PartialSelfing.ValidInput r.dimension r.generations r.selfing r.outcross r.initial := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-partial-selfing-check-v1"),
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

private theorem ratEntry_encodeEntry (value : Rat) :
    ratEntry (encodeEntry value) = .ok value :=
  RationalWire.decode_strictPrint value

private theorem list_ratArray_encode (values : List Rat) :
    (values.map encodeEntry).mapM ratEntry = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ratEntry_encodeEntry, ih]

private theorem ratArray_encodeArray (values : Array Rat) :
    ratArray (encodeArray values) = .ok values := by
  have hl := list_ratArray_encode values.toList
  change Array.mapM ratEntry (values.map encodeEntry) = _
  show (Array.mapM ratEntry (values.map encodeEntry)) = _
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

private theorem list_table_encode (values : List (Array Rat)) :
    (values.map encodeArray).mapM ratArray = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ratArray_encodeArray, ih]

private theorem ratTable_encode (values : Array (Array Rat)) :
    ratTable (.arr (values.map encodeArray)) = .ok values := by
  have hl := list_table_encode values.toList
  change Array.mapM ratArray (values.map encodeArray) = _
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

private theorem list_labels_encode (values : List String) :
    (values.map Json.str).mapM Json.getStr? = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ih, Json.getStr?]

private theorem labelArray_encode (values : Array String) :
    labelArray (.arr (values.map Json.str)) = .ok values := by
  have hl := list_labels_encode values.toList
  change Array.mapM Json.getStr? (values.map Json.str) = _
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hdq : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hdi : (inputFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [inputFields]
  have hs1 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("schema", Json.str "rhone-partial-selfing-v1") ∈ requestFields r))
  have hs2 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("model", Json.str "partial-selfing-unrelated-outcross-environment") ∈
      requestFields r))
  have hs3 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("comparison_semantics", Json.str "exact_fraction") ∈ requestFields r))
  have hs4 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("time_unit", Json.str "discrete-generation") ∈ requestFields r))
  have hs5 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("founder_identity", Json.str "explicit-copy-label-equality-IBD") ∈ requestFields r))
  have hs6 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("outcross_environment",
      Json.str "constant-supplied-joint-law-current-marginals-not-assumed") ∈
      requestFields r))
  have hs7 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("law_coordinate_order", Json.str "a*d+b") ∈ requestFields r))
  have hs8 := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("outcross_coordinate_order", Json.str "((a*d+b)*d+c)*d+e") ∈ requestFields r))
  have hinput := mkObj_getObjVal hdq (by simp [requestFields] :
    ("request", Json.mkObj (inputFields r)) ∈ requestFields r)
  have hischema := getStr_of (mkObj_getObjVal hdi (by simp [inputFields, toJson] :
    ("schema", Json.str "rhone-partial-selfing-request-v1") ∈ inputFields r))
  have hlabels := mkObj_getObjVal hdi (by simp [inputFields] :
    ("founder_labels", Json.arr (r.labels.map Json.str)) ∈ inputFields r)
  have hgen := getNat_of (mkObj_getObjVal hdi (by simp [inputFields] :
    ("generations", toJson r.generations) ∈ inputFields r))
  have hprov := getStr_of (mkObj_getObjVal hdi (by simp [inputFields] :
    ("parameter_provenance", Json.str r.provenance) ∈ inputFields r))
  have hself := rat_of (mkObj_getObjVal hdi (by simp [inputFields] :
    ("selfing_fraction", encodeEntry r.selfing) ∈ inputFields r))
  have hp := mkObj_getObjVal hdi (by simp [inputFields] :
    ("initial_diploid_law", encodeArray r.initial) ∈ inputFields r)
  have hq := mkObj_getObjVal hdi (by simp [inputFields] :
    ("outcross_parent_pair_law", encodeArray r.outcross) ∈ inputFields r)
  have htable := mkObj_getObjVal hdq (by simp [requestFields] :
    ("generation_laws", Json.arr (r.table.map encodeArray)) ∈ requestFields r)
  have hmoments := mkObj_getObjVal hdq (by simp [requestFields] :
    ("inbreeding", encodeArray r.moments) ∈ requestFields r)
  have heq := rat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("equilibrium_inbreeding", encodeEntry r.equilibrium) ∈ requestFields r))
  have hkin := rat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("outcross_kinship", encodeEntry r.kinship) ∈ requestFields r))
  have hlab' : ((Json.mkObj (inputFields r)).getObjVal? "founder_labels").bind labelArray =
      .ok r.labels := by
    rw [hlabels]
    exact labelArray_encode r.labels
  have hp' : ((Json.mkObj (inputFields r)).getObjVal? "initial_diploid_law").bind
      ratArray = .ok r.initial := by
    rw [hp]
    exact ratArray_encodeArray r.initial
  have hq' : ((Json.mkObj (inputFields r)).getObjVal? "outcross_parent_pair_law").bind
      ratArray = .ok r.outcross := by
    rw [hq]
    exact ratArray_encodeArray r.outcross
  have ht' : ((Json.mkObj (requestFields r)).getObjVal? "generation_laws").bind ratTable =
      .ok r.table := by
    rw [htable]
    exact ratTable_encode r.table
  have hm' : ((Json.mkObj (requestFields r)).getObjVal? "inbreeding").bind ratArray =
      .ok r.moments := by
    rw [hmoments]
    exact ratArray_encodeArray r.moments
  simp only [encode] at *
  simp [decode, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hinput, hischema, hlab', hgen,
    hprov, hself, hp', hq', ht', hm', heq, hkin]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then .ok (r.check, r.count)
      else .error "invalid complete supplied genetic laws" := by
  simp [decision, decode_encode]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.count)) := by
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (houtside : r.valid = false) :
    requestAst (encode r) = .error "invalid complete supplied genetic laws" := by
  simp [requestAst, decision_encode, houtside, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (r.check, r.count) ∧ requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, r.count) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout, hout ▸ requestAst_encode r hvalid⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧ r.check = true ∧
      count = r.count ∧ requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  exact ⟨r, hdecode, hvalid, hpair.1.symm, hpair.2, hencode⟩

theorem requestAst_encode_accept_sound (r : Request) (count : Nat)
    (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    r.valid = true ∧ r.check = true ∧ count = r.count := by
  obtain ⟨decoded, hdecode, hvalid, hcheck, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode] at hdecode
  cases hdecode
  exact ⟨hvalid, hcheck, hcount⟩

theorem requestAst_accept_request (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      PartialSelfing.ValidInput r.dimension r.generations r.selfing r.outcross r.initial ∧
      PartialSelfing.check r.dimension r.generations r.selfing r.outcross r.initial
        r.environment r.table r.moments r.equilibrium r.kinship = true := by
  obtain ⟨r, hdecode, hvalid, hcheck, -, -⟩ := requestAst_accept_sound doc count haccept
  exact ⟨r, hdecode, ((Request.valid_iff r).mp hvalid).2.2.2.2.2, hcheck⟩

open Dynamics.MendelianIBD in
theorem requestAst_accept_law_cast (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      (∀ k : Nat, k ≤ r.generations → ∀ z : PartialSelfing.Diploid r.dimension,
        (PartialSelfing.dipLaw r.dimension (r.table.getD k #[]) z : Real) =
          partialSelfingGeneration (r.selfing : Real)
            (fun _ xy => (PartialSelfing.parentLaw r.dimension r.outcross xy : Real))
            (fun x => (PartialSelfing.dipLaw r.dimension r.initial x : Real)) k z) ∧
      (∀ k : Fin (r.generations + 1), (r.moments.getD k 0 : Real) = founderIbd
        (partialSelfingGeneration (r.selfing : Real)
          (fun _ xy => (PartialSelfing.parentLaw r.dimension r.outcross xy : Real))
          (fun x => (PartialSelfing.dipLaw r.dimension r.initial x : Real)) k) id) := by
  obtain ⟨r, hdecode, hvalid, hcheck, -, -⟩ := requestAst_accept_sound doc count haccept
  exact ⟨r, hdecode,
    fun k hk z => PartialSelfing.check_law_cast _ _ _ _ _ _ _ _ _ _ hcheck k hk z,
    fun k => PartialSelfing.check_moment_cast _ _ _ _ _ _ _ _ _ _ hcheck k⟩

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.PartialSelfingWire
