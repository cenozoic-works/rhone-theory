/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.EffectiveSizeWire
public import Rhone.Computation.EffectiveSizeProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the effective-size reader -/

@[expose] public section
namespace Rhone.Computation.EffectiveSizeWire
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

private theorem some_getD {o : Option Rat} {q : Rat} (h : o = some q) :
    o = some (o.getD 0) := by
  subst h
  rfl

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ (∃ value : Rat, r.query.value = some value) ∧ r.query.entries ≤ 4096 := by
  unfold Request.valid
  rw [Bool.and_eq_true, decide_eq_true_iff, Option.isSome_iff_exists]

theorem Query.value_eq_none_iff (q : Query) :
    q.value = none ↔ match q with
      | .harmonic sizes => sizes = [] ∨ ∃ x ∈ sizes, x ≤ 0
      | .unequalSex males females => males = 0 ∨ females = 0
      | .variance p v => ¬ (0 < p ∧ p < 1 ∧ 0 < v)
      | .offspring copies sigma2 => ¬ (2 ≤ copies ∧ 0 < sigma2) := by
  cases q with
  | harmonic sizes => exact EffectiveSize.harmonicMean_eq_none_iff sizes
  | unequalSex males females => exact EffectiveSize.unequalSexEffective_eq_none_iff males females
  | variance p v => exact EffectiveSize.varianceEffective_eq_none_iff p v
  | offspring copies sigma2 =>
    exact EffectiveSize.offspringVarianceEffective_eq_none_iff copies sigma2

theorem Request.check_iff (r : Request) :
    r.check = true ↔ r.query.value = some r.claim := by
  unfold Request.check
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-effective-size-check-v1"),
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

private theorem fields_pairwise (r : Request) :
    (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  obtain ⟨q, claim⟩ := r
  cases q <;> simp [requestFields, Query.fields]

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value :=
  mkObj_getObjVal (fields_pairwise r) hmem

private theorem rowEntry_encodeRat (value : Rat) :
    rowEntry (encodeRat value) = .ok value :=
  RationalWire.decode_strictPrint value

private theorem list_row_encode (values : List Rat) :
    (values.map encodeRat).mapM rowEntry = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, rowEntry_encodeRat, ih]

theorem ratArray_encode (values : List Rat) :
    ratArray (encodeRats values) = .ok values.toArray := by
  have hl := list_row_encode values
  unfold ratArray encodeRats
  change (Except.ok (values.toArray.map encodeRat) : Except String (Array Json)) >>= _ = _
  rw [ok_bind, Array.mapM_eq_mapM_toList, Array.toList_map, List.toList_toArray, hl]
  simp

private theorem query_encode (r : Request) :
    query (encode r) r.query.name = .ok r.query := by
  obtain ⟨q, claim⟩ := r
  cases q with
  | harmonic sizes =>
    have h : ((encode ⟨.harmonic sizes, claim⟩).getObjVal? "sizes").bind ratArray =
        .ok sizes.toArray := by
      rw [encode_getObjVal (r := ⟨.harmonic sizes, claim⟩) (name := "sizes")
        (value := encodeRats sizes) (by simp [requestFields, Query.fields])]
      exact ratArray_encode sizes
    simp [query, Query.name, h]
  | unequalSex males females =>
    have hm := getNat_of (encode_getObjVal (r := ⟨.unequalSex males females, claim⟩)
      (name := "breeding_males") (value := toJson males)
      (by simp [requestFields, Query.fields]))
    have hf := getNat_of (encode_getObjVal (r := ⟨.unequalSex males females, claim⟩)
      (name := "breeding_females") (value := toJson females)
      (by simp [requestFields, Query.fields]))
    simp [query, Query.name, hm, hf]
  | variance p v =>
    have hp := rat_of (encode_getObjVal (r := ⟨.variance p v, claim⟩)
      (name := "allele_frequency") (value := encodeRat p)
      (by simp [requestFields, Query.fields]))
    have hv := rat_of (encode_getObjVal (r := ⟨.variance p v, claim⟩)
      (name := "frequency_variance") (value := encodeRat v)
      (by simp [requestFields, Query.fields]))
    simp [query, Query.name, hp, hv]
  | offspring copies sigma2 =>
    have hn := getNat_of (encode_getObjVal (r := ⟨.offspring copies sigma2, claim⟩)
      (name := "gene_copies") (value := toJson copies)
      (by simp [requestFields, Query.fields]))
    have hs := rat_of (encode_getObjVal (r := ⟨.offspring copies sigma2, claim⟩)
      (name := "offspring_variance") (value := encodeRat sigma2)
      (by simp [requestFields, Query.fields]))
    simp [query, Query.name, hn, hs]

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-effective-size-v1") (by simp [requestFields, toJson]))
  have hquantity := getStr_of (encode_getObjVal (r := r) (name := "quantity")
    (value := .str r.query.name) (by simp [requestFields]))
  have hclaim := rat_of (encode_getObjVal (r := r) (name := "effective_size")
    (value := encodeRat r.claim) (by simp [requestFields]))
  simp [decode, hschema, hquantity, query_encode r, hclaim]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then .ok (r.check, 1)
      else .error "unsupported effective-size request domain" := by
  simp [decision, decode_encode r]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, 1)) := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported effective-size request domain" := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (r.check, 1) ∧ requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, 1) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout, hout ▸ requestAst_encode r hvalid⟩

theorem requestAst_accept_iff (doc : Json) (count : Nat) :
    requestAst doc = .ok (stamp (true, count)) ↔
      ∃ r : Request, decode doc = .ok r ∧ r.query.entries ≤ 4096 ∧
        r.query.value = some r.claim ∧ count = 1 := by
  constructor
  · intro haccept
    obtain ⟨r, hdecode, hvalid, hout, -⟩ := requestAst_ok doc _ haccept
    have hpair := stamp_injective hout
    simp only [Prod.mk.injEq] at hpair
    exact ⟨r, hdecode, ((Request.valid_iff r).mp hvalid).2,
      (Request.check_iff r).mp hpair.1.symm, hpair.2⟩
  · rintro ⟨r, hdecode, hsize, hvalue, rfl⟩
    have hvalid : r.valid = true := (Request.valid_iff r).mpr ⟨⟨_, hvalue⟩, hsize⟩
    have hcheck : r.check = true := (Request.check_iff r).mpr hvalue
    simp [requestAst, decision, hdecode, hvalid, hcheck, Except.map]

theorem requestAst_accept_spec (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      (∀ sizes, r.query = .harmonic sizes →
        (r.claim : ℝ) = Rhone.MarkovChain.EffectiveSize.harmonicSize
          (EffectiveSize.sizesReal sizes)) ∧
      (∀ males females, r.query = .unequalSex males females →
        (r.claim : ℝ) = Rhone.MarkovChain.EffectiveSize.coalescenceEffective
          (Rhone.MarkovChain.EffectiveSize.sexPairCoalescence males females)) ∧
      (∀ p v, r.query = .variance p v →
        (r.claim : ℝ) = Rhone.MarkovChain.EffectiveSize.varianceEffective (p : ℝ) (v : ℝ)) ∧
      (∀ copies sigma2, r.query = .offspring copies sigma2 →
        (r.claim : ℝ) = Rhone.MarkovChain.EffectiveSize.eigenvalueEffective
          (1 - (sigma2 : ℝ) / ((copies : ℝ) - 1))) := by
  obtain ⟨r, hdecode, -, hvalue, -⟩ := (requestAst_accept_iff doc count).mp haccept
  refine ⟨r, hdecode, ?_, ?_, ?_, ?_⟩
  · intro sizes hquery
    rw [hquery] at hvalue
    have hv : EffectiveSize.harmonicMean sizes = some r.claim := hvalue
    have hnone : ¬ (sizes = [] ∨ ∃ x ∈ sizes, x ≤ 0) := by
      intro h
      rw [(EffectiveSize.harmonicMean_eq_none_iff sizes).mpr h] at hv
      cases hv
    obtain ⟨q, hq, hqe, -⟩ := EffectiveSize.harmonicMean_eq sizes
      (fun h => hnone (Or.inl h))
      (fun x hx => lt_of_not_ge fun hle => hnone (Or.inr ⟨x, hx, hle⟩))
    rw [← Option.some.inj (hq.symm.trans hv)]
    exact hqe
  · intro males females hquery
    rw [hquery] at hvalue
    have hv : EffectiveSize.unequalSexEffective males females = some r.claim := hvalue
    have hnone : ¬ (males = 0 ∨ females = 0) := by
      intro h
      rw [(EffectiveSize.unequalSexEffective_eq_none_iff males females).mpr h] at hv
      cases hv
    obtain ⟨q, hq, hqe, -⟩ := EffectiveSize.unequalSexEffective_eq males females
      (Nat.pos_of_ne_zero fun h => hnone (Or.inl h))
      (Nat.pos_of_ne_zero fun h => hnone (Or.inr h))
    rw [← Option.some.inj (hq.symm.trans hv)]
    exact hqe
  · intro p v hquery
    rw [hquery] at hvalue
    have hv : EffectiveSize.varianceEffective p v = some r.claim := hvalue
    have hdomain : 0 < p ∧ p < 1 ∧ 0 < v := by
      by_contra h
      rw [(EffectiveSize.varianceEffective_eq_none_iff p v).mpr h] at hv
      cases hv
    obtain ⟨q, hq, hqe⟩ := EffectiveSize.varianceEffective_eq p v hdomain.1 hdomain.2.1
      hdomain.2.2
    rw [← Option.some.inj (hq.symm.trans hv)]
    exact hqe
  · intro copies sigma2 hquery
    rw [hquery] at hvalue
    have hv : EffectiveSize.offspringVarianceEffective copies sigma2 = some r.claim := hvalue
    have hdomain : 2 ≤ copies ∧ 0 < sigma2 := by
      by_contra h
      rw [(EffectiveSize.offspringVarianceEffective_eq_none_iff copies sigma2).mpr h] at hv
      cases hv
    obtain ⟨q, hq, hqe⟩ := EffectiveSize.offspringVarianceEffective_eq copies sigma2
      hdomain.1 hdomain.2
    rw [← Option.some.inj (hq.symm.trans hv)]
    exact hqe

theorem requestAst_ofFormula (q : Query) (value : Rat) (hvalue : q.value = some value)
    (hsize : q.entries ≤ 4096) :
    requestAst (encode (Request.ofFormula q)) = .ok (stamp (true, 1)) := by
  have hvalid : (Request.ofFormula q).valid = true :=
    (Request.valid_iff _).mpr ⟨⟨value, hvalue⟩, hsize⟩
  have hcheck : (Request.ofFormula q).check = true :=
    (Request.check_iff _).mpr (some_getD hvalue)
  rw [requestAst_encode _ hvalid, hcheck]

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.EffectiveSizeWire
