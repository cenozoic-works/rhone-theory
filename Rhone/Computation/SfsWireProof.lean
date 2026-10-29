/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SfsWire
public import Rhone.Computation.SfsAcceptanceProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the `check_sfs` request reader -/

@[expose] public section
namespace Rhone.Computation.SfsWire
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
    (h : object.getObjVal? name = .ok (.str (RationalWire.strictPrint value))) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ 2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta := by
  simp [Request.valid]

theorem Request.claim_ofFormula (n : Nat) (theta : Rat) :
    (Request.ofFormula n theta).claim = Sfs.reportValues n theta := rfl

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-kernel-sfs-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("checker", toJson "Rhone.Computation.Sfs.checkReport"),
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

private theorem bin_encodeBin (value : Rat) (position : Nat) :
    bin (encodeBin (value, position), position) = .ok value := by
  have hd : (binFields (value, position)).Pairwise
      (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [binFields]
  have hcopies := getNat_of (mkObj_getObjVal hd (by simp [binFields] :
    ("derived_copies", toJson (position + 1)) ∈ binFields (value, position)))
  have hmean := rat_of (mkObj_getObjVal hd (by simp [binFields] :
    ("mean", Json.str (RationalWire.strictPrint value)) ∈ binFields (value, position)))
  simp only [encodeBin] at *
  simp [bin, hcopies, hmean]

private theorem list_bins_encode (values : List Rat) (start : Nat) :
    (((values.zipIdx start).map encodeBin).zipIdx start).mapM bin = .ok values := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih =>
    simp [List.mapM_cons, bin_encodeBin, ih (start + 1)]

theorem bins_encode (values : Array Rat) :
    (values.zipIdx.map encodeBin).zipIdx.mapM bin = .ok values := by
  have hl := list_bins_encode values.toList 0
  rw [Array.mapM_eq_mapM_toList]
  simp only [Array.toList_zipIdx, Array.toList_map]
  rw [hl]
  simp

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hdq : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hdr : (reportFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [reportFields]
  have hdc : (coefficientFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [coefficientFields]
  have hdm : (momentFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [momentFields]
  have hn := getNat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("gene_copies", toJson r.geneCopies) ∈ requestFields r))
  have htheta := rat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("theta", Json.str (RationalWire.strictPrint r.theta)) ∈ requestFields r))
  have hreport := mkObj_getObjVal hdq (by simp [requestFields] :
    ("report", Json.mkObj (reportFields r)) ∈ requestFields r)
  have hschema := getStr_of (mkObj_getObjVal hdr (by simp [reportFields, toJson] :
    ("schema", Json.str "rhone-sfs-v1") ∈ reportFields r))
  have hrn := getNat_of (mkObj_getObjVal hdr (by simp [reportFields] :
    ("gene_copies", toJson r.geneCopies) ∈ reportFields r))
  have hrtheta := rat_of (mkObj_getObjVal hdr (by simp [reportFields] :
    ("theta", Json.str (RationalWire.strictPrint r.theta)) ∈ reportFields r))
  have hcoefficients := mkObj_getObjVal hdr (by simp [reportFields] :
    ("coefficients", Json.mkObj (coefficientFields r)) ∈ reportFields r)
  have hmoments := mkObj_getObjVal hdr (by simp [reportFields] :
    ("null_moments", Json.mkObj (momentFields r)) ∈ reportFields r)
  have hspectrum := mkObj_getObjVal hdr (by simp [reportFields] :
    ("expected_spectrum", Json.arr (r.spectrum.zipIdx.map encodeBin)) ∈ reportFields r)
  have ha1 := rat_of (mkObj_getObjVal hdc (by simp [coefficientFields] :
    ("a1", Json.str (RationalWire.strictPrint r.a1)) ∈ coefficientFields r))
  have ha2 := rat_of (mkObj_getObjVal hdc (by simp [coefficientFields] :
    ("a2", Json.str (RationalWire.strictPrint r.a2)) ∈ coefficientFields r))
  have hb1 := rat_of (mkObj_getObjVal hdc (by simp [coefficientFields] :
    ("b1", Json.str (RationalWire.strictPrint r.b1)) ∈ coefficientFields r))
  have hb2 := rat_of (mkObj_getObjVal hdc (by simp [coefficientFields] :
    ("b2", Json.str (RationalWire.strictPrint r.b2)) ∈ coefficientFields r))
  have hm1 := rat_of (mkObj_getObjVal hdm (by simp [momentFields] :
    ("mean_segregating", Json.str (RationalWire.strictPrint r.meanSegregating)) ∈
      momentFields r))
  have hm2 := rat_of (mkObj_getObjVal hdm (by simp [momentFields] :
    ("variance_segregating", Json.str (RationalWire.strictPrint r.varianceSegregating)) ∈
      momentFields r))
  have hm3 := rat_of (mkObj_getObjVal hdm (by simp [momentFields] :
    ("mean_pairwise", Json.str (RationalWire.strictPrint r.meanPairwise)) ∈
      momentFields r))
  have hm4 := rat_of (mkObj_getObjVal hdm (by simp [momentFields] :
    ("second_moment_pairwise", Json.str (RationalWire.strictPrint r.secondMomentPairwise)) ∈
      momentFields r))
  have hm5 := rat_of (mkObj_getObjVal hdm (by simp [momentFields] :
    ("variance_pairwise", Json.str (RationalWire.strictPrint r.variancePairwise)) ∈
      momentFields r))
  have hbins : ((Json.mkObj (reportFields r)).getObjVal? "expected_spectrum").bind
      Json.getArr? = .ok (r.spectrum.zipIdx.map encodeBin) := by
    rw [hspectrum]
    rfl
  simp only [encode] at *
  simp [decode, hn, htheta, hreport, hschema, hrn, hrtheta, hcoefficients, hmoments,
    ha1, ha2, hb1, hb2, hm1, hm2, hm3, hm4, hm5, hbins, bins_encode]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then
      .ok (Sfs.checkReport r.geneCopies r.theta r.claim, r.claim.size)
      else .error "unsupported sample size or negative theta" := by
  simp [decision, decode_encode]

theorem requestAst_encode (r : Request) (hlower : 2 ≤ r.geneCopies)
    (hupper : r.geneCopies ≤ 4096) (htheta : 0 ≤ r.theta) :
    requestAst (encode r) =
      .ok (stamp (Sfs.checkReport r.geneCopies r.theta r.claim, r.claim.size)) := by
  have hvalid : r.valid = true := (Request.valid_iff r).mpr ⟨hlower, hupper, htheta⟩
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request)
    (houtside : ¬ (2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta)) :
    requestAst (encode r) = .error "unsupported sample size or negative theta" := by
  have hvalid : r.valid = false := by
    cases h : r.valid
    · rfl
    · exact absurd ((Request.valid_iff r).mp h) houtside
  simp [requestAst, decision_encode, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧
      2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta ∧
      out = stamp (Sfs.checkReport r.geneCopies r.theta r.claim, r.claim.size) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      obtain ⟨hlower, hupper, htheta⟩ := (Request.valid_iff r).mp hvalid
      have hout : out =
          stamp (Sfs.checkReport r.geneCopies r.theta r.claim, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hlower, hupper, htheta, hout,
        hout ▸ requestAst_encode r hlower hupper htheta⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta ∧
      r.claim = Sfs.reportValues r.geneCopies r.theta ∧ count = r.claim.size ∧
      requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hlower, hupper, htheta, hout, hencode⟩ :=
    requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  exact ⟨r, hdecode, hlower, hupper, htheta,
    (Sfs.checkReport_iff _ _ _).mp hpair.1.symm, hpair.2, hencode⟩

theorem requestAst_encode_accept_sound (r : Request) (count : Nat)
    (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    2 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 ≤ r.theta ∧
      r.claim = Sfs.reportValues r.geneCopies r.theta ∧ count = r.claim.size := by
  obtain ⟨decoded, hdecode, hlower, hupper, htheta, hclaim, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode] at hdecode
  cases hdecode
  exact ⟨hlower, hupper, htheta, hclaim, hcount⟩

theorem requestAst_ofFormula (n : Nat) (theta : Rat) (hlower : 2 ≤ n) (hupper : n ≤ 4096)
    (htheta : 0 ≤ theta) :
    requestAst (encode (Request.ofFormula n theta)) =
      .ok (stamp (true, (Sfs.reportValues n theta).size)) := by
  have h := requestAst_encode (Request.ofFormula n theta) hlower hupper htheta
  rw [Request.claim_ofFormula] at h
  rw [h]
  change Except.ok (stamp (Sfs.checkReport n theta (Sfs.reportValues n theta), _)) = _
  rw [Sfs.checkReport_complete]

theorem requestAst_accept_request (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      (⟨r.geneCopies, r.theta⟩ : Sfs.Request).valid = true ∧
      (⟨r.geneCopies, r.theta⟩ : Sfs.Request).check r.claim = true ∧ 0 ≤ r.theta := by
  obtain ⟨r, hdecode, hlower, hupper, htheta, hclaim, -, -⟩ :=
    requestAst_accept_sound doc count haccept
  exact ⟨r, hdecode, (Sfs.Request.valid_iff _).mpr ⟨hlower, hupper, htheta⟩,
    (Sfs.checkReport_iff _ _ _).mpr hclaim, htheta⟩

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.SfsWire
