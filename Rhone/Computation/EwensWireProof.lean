/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.EwensWire
public import Rhone.Computation.EwensProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the Ewens sampling reader -/

@[expose] public section
namespace Rhone.Computation.EwensWire
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

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value :=
  mkObj_getObjVal (by simp [requestFields]) hmem

private theorem some_getD {o : Option Rat} {q : Rat} (h : o = some q) :
    o = some (o.getD 0) := by
  subst h
  rfl

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ 0 < r.theta ∧ (∀ x ∈ r.parts, 0 < x) ∧ r.parts.sum ≤ 1024 := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem Request.check_iff (r : Request) :
    r.check = true ↔ Ewens.esf r.theta r.parts = some r.partitionProbability ∧
      Ewens.alleleCountProb r.theta r.parts.sum r.parts.length =
        some r.alleleCountProbability ∧
      Ewens.expectedAlleles r.theta r.parts.sum = some r.expectedAlleles := by
  unfold Request.check
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-ewens-check-v1"),
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
  obtain ⟨a, c⟩ := first
  obtain ⟨a', c'⟩ := second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2
  simp [h1, h2]

private theorem getNat_toJson (value : Nat) : Json.getNat? (toJson value) = .ok value := rfl

private theorem list_nat_encode (values : List Nat) :
    (values.map (toJson : Nat → Json)).mapM Json.getNat? = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, getNat_toJson, ih]

theorem natArray_encode (values : List Nat) :
    natArray (encodeNats values) = .ok values.toArray := by
  have hl := list_nat_encode values
  unfold natArray encodeNats
  change (Except.ok (values.toArray.map toJson) : Except String (Array Json)) >>= _ = _
  rw [ok_bind, Array.mapM_eq_mapM_toList, Array.toList_map, List.toList_toArray, hl]
  simp

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-ewens-v1") (by simp [requestFields, toJson]))
  have htheta := rat_of (encode_getObjVal (r := r) (name := "theta")
    (value := encodeRat r.theta) (by simp [requestFields]))
  have hparts : ((encode r).getObjVal? "partition").bind natArray = .ok r.parts.toArray := by
    rw [encode_getObjVal (r := r) (name := "partition") (value := encodeNats r.parts)
      (by simp [requestFields])]
    exact natArray_encode r.parts
  have h1 := rat_of (encode_getObjVal (r := r) (name := "partition_probability")
    (value := encodeRat r.partitionProbability) (by simp [requestFields]))
  have h2 := rat_of (encode_getObjVal (r := r) (name := "allele_count_probability")
    (value := encodeRat r.alleleCountProbability) (by simp [requestFields]))
  have h3 := rat_of (encode_getObjVal (r := r) (name := "expected_alleles")
    (value := encodeRat r.expectedAlleles) (by simp [requestFields]))
  simp [decode, hschema, htheta, hparts, h1, h2, h3]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then .ok (r.check, r.claim.size)
      else .error "unsupported Ewens request domain" := by
  simp [decision, decode_encode r]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.claim.size)) := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported Ewens request domain" := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (r.check, r.claim.size) ∧ requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout, hout ▸ requestAst_encode r hvalid⟩

theorem requestAst_accept_iff (doc : Json) (count : Nat) :
    requestAst doc = .ok (stamp (true, count)) ↔
      ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
        Ewens.esf r.theta r.parts = some r.partitionProbability ∧
        Ewens.alleleCountProb r.theta r.parts.sum r.parts.length =
          some r.alleleCountProbability ∧
        Ewens.expectedAlleles r.theta r.parts.sum = some r.expectedAlleles ∧
        count = 3 := by
  constructor
  · intro haccept
    obtain ⟨r, hdecode, hvalid, hout, -⟩ := requestAst_ok doc _ haccept
    have hpair := stamp_injective hout
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨h1, h2, h3⟩ := (Request.check_iff r).mp hpair.1.symm
    exact ⟨r, hdecode, hvalid, h1, h2, h3, hpair.2⟩
  · rintro ⟨r, hdecode, hvalid, h1, h2, h3, rfl⟩
    have hcheck : r.check = true := (Request.check_iff r).mpr ⟨h1, h2, h3⟩
    simp [requestAst, decision, hdecode, hvalid, hcheck, Except.map, Request.claim]

theorem requestAst_accept_spec (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 < r.theta ∧
      ∃ hparts : ∀ x ∈ r.parts, 0 < x,
        r.partitionProbability = Rhone.Probability.esf r.theta (Ewens.toPartition r.parts hparts) ∧
        r.alleleCountProbability =
          ∑ p ∈ (Finset.univ : Finset (Nat.Partition r.parts.sum)).filter
            (fun p => p.parts.card = r.parts.length), Rhone.Probability.esf r.theta p ∧
        r.expectedAlleles = ∑ p : Nat.Partition r.parts.sum,
          (p.parts.card : ℚ) * Rhone.Probability.esf r.theta p := by
  obtain ⟨r, hdecode, hvalid, h1, h2, h3, -⟩ := (requestAst_accept_iff doc count).mp haccept
  obtain ⟨htheta, hparts, -⟩ := (Request.valid_iff r).mp hvalid
  refine ⟨r, hdecode, htheta, hparts, ?_, ?_, ?_⟩
  · exact Option.some.inj (h1.symm.trans (Ewens.esf_eq_some r.theta htheta r.parts hparts))
  · exact Option.some.inj (h2.symm.trans (Ewens.alleleCountProb_eq_some r.theta htheta _ _))
  · exact Option.some.inj (h3.symm.trans (Ewens.expectedAlleles_eq_some r.theta htheta _))

theorem requestAst_ofFormula (theta : Rat) (parts : List Nat) (htheta : 0 < theta)
    (hparts : ∀ x ∈ parts, 0 < x) (hsize : parts.sum ≤ 1024) :
    requestAst (encode (Request.ofFormula theta parts)) = .ok (stamp (true, 3)) := by
  have hvalid : (Request.ofFormula theta parts).valid = true :=
    (Request.valid_iff _).mpr ⟨htheta, hparts, hsize⟩
  have hcheck : (Request.ofFormula theta parts).check = true :=
    (Request.check_iff _).mpr
      ⟨some_getD (Ewens.esf_eq_some theta htheta parts hparts),
        some_getD (Ewens.alleleCountProb_eq_some theta htheta parts.sum parts.length),
        some_getD (Ewens.expectedAlleles_eq_some theta htheta parts.sum)⟩
  rw [requestAst_encode _ hvalid, hcheck]
  rfl

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.EwensWire
