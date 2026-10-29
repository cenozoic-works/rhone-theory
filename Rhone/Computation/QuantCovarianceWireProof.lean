/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.QuantCovarianceWire
public import Rhone.Computation.QuantCovarianceProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the single-locus variance and covariance reader -/

@[expose] public section
namespace Rhone.Computation.QuantCovarianceWire
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
    r.valid = true ↔ 0 ≤ r.frequency ∧ r.frequency ≤ 1 :=
  QuantCovariance.validFreq_iff r.frequency

theorem Request.check_iff (r : Request) :
    r.check = true ↔
      QuantCovariance.varA r.frequency r.values = some r.additiveVariance ∧
      QuantCovariance.varD r.frequency r.values = some r.dominanceVariance ∧
      QuantCovariance.parentOffspringCov r.frequency r.values = some r.parentOffspring ∧
      QuantCovariance.halfSibCov r.frequency r.values = some r.halfSib ∧
      QuantCovariance.fullSibCov r.frequency r.values = some r.fullSib := by
  unfold Request.check
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-quant-covariance-check-v1"),
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

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-quant-covariance-v1") (by simp [requestFields, toJson]))
  have hp := rat_of (encode_getObjVal (r := r) (name := "allele_frequency")
    (value := encodeRat r.frequency) (by simp [requestFields]))
  have h0 := rat_of (encode_getObjVal (r := r) (name := "genotypic_value_0")
    (value := encodeRat r.g0) (by simp [requestFields]))
  have h1 := rat_of (encode_getObjVal (r := r) (name := "genotypic_value_1")
    (value := encodeRat r.g1) (by simp [requestFields]))
  have h2 := rat_of (encode_getObjVal (r := r) (name := "genotypic_value_2")
    (value := encodeRat r.g2) (by simp [requestFields]))
  have ha := rat_of (encode_getObjVal (r := r) (name := "additive_variance")
    (value := encodeRat r.additiveVariance) (by simp [requestFields]))
  have hd := rat_of (encode_getObjVal (r := r) (name := "dominance_variance")
    (value := encodeRat r.dominanceVariance) (by simp [requestFields]))
  have hpo := rat_of (encode_getObjVal (r := r) (name := "parent_offspring_covariance")
    (value := encodeRat r.parentOffspring) (by simp [requestFields]))
  have hhs := rat_of (encode_getObjVal (r := r) (name := "half_sib_covariance")
    (value := encodeRat r.halfSib) (by simp [requestFields]))
  have hfs := rat_of (encode_getObjVal (r := r) (name := "full_sib_covariance")
    (value := encodeRat r.fullSib) (by simp [requestFields]))
  simp [decode, hschema, hp, h0, h1, h2, ha, hd, hpo, hhs, hfs]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then .ok (r.check, r.claim.size)
      else .error "unsupported quantitative covariance request domain" := by
  simp [decision, decode_encode r]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.claim.size)) := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hvalid : r.valid = false) :
    requestAst (encode r) =
      .error "unsupported quantitative covariance request domain" := by
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
        QuantCovariance.varA r.frequency r.values = some r.additiveVariance ∧
        QuantCovariance.varD r.frequency r.values = some r.dominanceVariance ∧
        QuantCovariance.parentOffspringCov r.frequency r.values = some r.parentOffspring ∧
        QuantCovariance.halfSibCov r.frequency r.values = some r.halfSib ∧
        QuantCovariance.fullSibCov r.frequency r.values = some r.fullSib ∧
        count = 5 := by
  constructor
  · intro haccept
    obtain ⟨r, hdecode, hvalid, hout, -⟩ := requestAst_ok doc _ haccept
    have hpair := stamp_injective hout
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Request.check_iff r).mp hpair.1.symm
    exact ⟨r, hdecode, hvalid, h1, h2, h3, h4, h5, hpair.2⟩
  · rintro ⟨r, hdecode, hvalid, h1, h2, h3, h4, h5, rfl⟩
    have hcheck : r.check = true := (Request.check_iff r).mpr ⟨h1, h2, h3, h4, h5⟩
    simp [requestAst, decision, hdecode, hvalid, hcheck, Except.map, Request.claim]

theorem requestAst_accept_spec (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 ≤ r.frequency ∧ r.frequency ≤ 1 ∧
      (r.additiveVariance : ℝ) =
        Rhone.Statistics.varA (r.frequency : ℝ) (QuantCovariance.toReal r.values) ∧
      (r.dominanceVariance : ℝ) =
        Rhone.Statistics.varD (r.frequency : ℝ) (QuantCovariance.toReal r.values) ∧
      (r.parentOffspring : ℝ) =
        Rhone.Statistics.parentOffspringCov (r.frequency : ℝ) (QuantCovariance.toReal r.values) ∧
      (r.halfSib : ℝ) =
        Rhone.Statistics.halfSibCov (r.frequency : ℝ) (QuantCovariance.toReal r.values) ∧
      (r.fullSib : ℝ) =
        Rhone.Statistics.fullSibCov (r.frequency : ℝ) (QuantCovariance.toReal r.values) ∧
      r.parentOffspring = r.additiveVariance / 2 ∧ r.halfSib = r.additiveVariance / 4 ∧
      r.fullSib = r.additiveVariance / 2 + r.dominanceVariance / 4 := by
  obtain ⟨r, hdecode, hvalid, h1, h2, h3, h4, h5, -⟩ :=
    (requestAst_accept_iff doc count).mp haccept
  obtain ⟨hlower, hupper⟩ := (Request.valid_iff r).mp hvalid
  obtain ⟨a, ha, hae⟩ := QuantCovariance.varA_eq r.frequency r.values hlower hupper
  obtain ⟨d, hd, hde⟩ := QuantCovariance.varD_eq r.frequency r.values hlower hupper
  obtain ⟨po, hpo, hpoe⟩ :=
    QuantCovariance.parentOffspringCov_eq r.frequency r.values hlower hupper
  obtain ⟨hs, hhs, hhse⟩ := QuantCovariance.halfSibCov_eq r.frequency r.values hlower hupper
  obtain ⟨fs, hfs, hfse⟩ := QuantCovariance.fullSibCov_eq r.frequency r.values hlower hupper
  obtain ⟨a', d', po', hs', fs', ha', hd', hpo', hhs', hfs', r1, r2, r3⟩ :=
    QuantCovariance.covariance_relations r.frequency r.values hlower hupper
  have ea : a = r.additiveVariance := Option.some.inj (ha.symm.trans h1)
  have ed : d = r.dominanceVariance := Option.some.inj (hd.symm.trans h2)
  have epo : po = r.parentOffspring := Option.some.inj (hpo.symm.trans h3)
  have ehs : hs = r.halfSib := Option.some.inj (hhs.symm.trans h4)
  have efs : fs = r.fullSib := Option.some.inj (hfs.symm.trans h5)
  have ea' : a' = r.additiveVariance := Option.some.inj (ha'.symm.trans h1)
  have ed' : d' = r.dominanceVariance := Option.some.inj (hd'.symm.trans h2)
  have epo' : po' = r.parentOffspring := Option.some.inj (hpo'.symm.trans h3)
  have ehs' : hs' = r.halfSib := Option.some.inj (hhs'.symm.trans h4)
  have efs' : fs' = r.fullSib := Option.some.inj (hfs'.symm.trans h5)
  subst ea ed epo ehs efs ea' ed' epo' ehs' efs'
  exact ⟨r, hdecode, hlower, hupper, hae, hde, hpoe, hhse, hfse, r1, r2, r3⟩

theorem requestAst_ofFormula (p g0 g1 g2 : Rat) (hlower : 0 ≤ p) (hupper : p ≤ 1) :
    requestAst (encode (Request.ofFormula p g0 g1 g2)) = .ok (stamp (true, 5)) := by
  have hvalid : (Request.ofFormula p g0 g1 g2).valid = true :=
    (Request.valid_iff _).mpr ⟨hlower, hupper⟩
  obtain ⟨a, ha, -⟩ := QuantCovariance.varA_eq p ⟨g0, g1, g2⟩ hlower hupper
  obtain ⟨d, hd, -⟩ := QuantCovariance.varD_eq p ⟨g0, g1, g2⟩ hlower hupper
  obtain ⟨po, hpo, -⟩ := QuantCovariance.parentOffspringCov_eq p ⟨g0, g1, g2⟩ hlower hupper
  obtain ⟨hs, hhs, -⟩ := QuantCovariance.halfSibCov_eq p ⟨g0, g1, g2⟩ hlower hupper
  obtain ⟨fs, hfs, -⟩ := QuantCovariance.fullSibCov_eq p ⟨g0, g1, g2⟩ hlower hupper
  have hcheck : (Request.ofFormula p g0 g1 g2).check = true :=
    (Request.check_iff _).mpr
      ⟨some_getD ha, some_getD hd, some_getD hpo, some_getD hhs, some_getD hfs⟩
  rw [requestAst_encode _ hvalid, hcheck]
  rfl

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.QuantCovarianceWire
