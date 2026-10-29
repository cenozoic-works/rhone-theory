/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsFull
public import Rhone.Computation.SfsWireProof
public import Rhone.Computation.SfsObservedCountsProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.WF

/-!
# Acceptance of the full SFS report

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thm 1.22; fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Computation.SfsFull
open Lean

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem except_ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    (Except.ok x : Except String α).bind f = f x := rfl

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

private theorem getNat_of {object : Json} {name : String} {value : Nat}
    (h : object.getObjVal? name = .ok (toJson value)) :
    object.getObjValAs? Nat name = .ok value := by
  change Json.getNat? ((object.getObjVal? name).toOption.getD .null) = _
  rw [h]
  rfl

private theorem getStr_of {object : Json} {name value : String}
    (h : object.getObjVal? name = .ok (.str value)) :
    object.getObjValAs? String name = .ok value := by
  change Json.getStr? ((object.getObjVal? name).toOption.getD .null) = _
  rw [h]
  rfl

private theorem rat_of {object : Json} {name : String} {value : Rat}
    (h : object.getObjVal? name = .ok (.str (RationalWire.strictPrint value))) :
    SfsWire.rat object name = .ok value := by
  rw [SfsWire.rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

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
    else Except.error "unsupported SFS report field") = Except.ok ()
  rw [ha]
  rfl

theorem fieldsAllowed_ok_iff (value : Json) (allowed : List String) :
    fieldsAllowed value allowed = .ok () ↔
      ∃ fields, value.getObj? = .ok fields ∧ ∀ p ∈ fields.toList, p.1 ∈ allowed := by
  cases hobj : value.getObj? with
  | error message => simp [fieldsAllowed, hobj]
  | ok fields => simp [fieldsAllowed, hobj]

private theorem observedFields_allowed (o : Observed) :
    fieldsAllowed (Json.mkObj (observedFields o)) observedKeys = .ok () := by
  apply fieldsAllowed_mkObj
  intro p hp
  simp only [observedFields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl) <;> simp [observedKeys]

private theorem coefficientFields_allowed (r : SfsWire.Request) :
    fieldsAllowed (Json.mkObj (SfsWire.coefficientFields r)) coefficientKeys = .ok () := by
  apply fieldsAllowed_mkObj
  intro p hp
  simp only [SfsWire.coefficientFields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl) <;> simp [coefficientKeys]

private theorem momentFields_allowed (r : SfsWire.Request) :
    fieldsAllowed (Json.mkObj (SfsWire.momentFields r)) momentKeys = .ok () := by
  apply fieldsAllowed_mkObj
  intro p hp
  simp only [SfsWire.momentFields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl) <;> simp [momentKeys]

private theorem reportFields_allowed (r : Request) :
    fieldsAllowed (Json.mkObj (reportFields r)) reportKeys = .ok () := by
  apply fieldsAllowed_mkObj
  intro p hp
  simp only [reportFields, SfsWire.reportFields, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) <;>
    simp [reportKeys]

private theorem binFields_allowed (entry : Rat × Nat) :
    fieldsAllowed (SfsWire.encodeBin entry) binKeys = .ok () := by
  apply fieldsAllowed_mkObj
  intro p hp
  simp only [SfsWire.binFields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl) <;> simp [binKeys]

private theorem nullFieldsAllowed_encode (r : Request) :
    nullFieldsAllowed (Json.mkObj (reportFields r)) = .ok () := by
  have hd : (reportFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [reportFields, SfsWire.reportFields]
  have hc := mkObj_getObjVal hd (by simp [reportFields, SfsWire.reportFields] :
    ("coefficients", Json.mkObj (SfsWire.coefficientFields r.base)) ∈ reportFields r)
  have hm := mkObj_getObjVal hd (by simp [reportFields, SfsWire.reportFields] :
    ("null_moments", Json.mkObj (SfsWire.momentFields r.base)) ∈ reportFields r)
  have hb := mkObj_getObjVal hd (by simp [reportFields, SfsWire.reportFields] :
    ("expected_spectrum", Json.arr (r.base.spectrum.zipIdx.map SfsWire.encodeBin)) ∈
      reportFields r)
  have hbins : ((Json.mkObj (reportFields r)).getObjVal? "expected_spectrum").bind
      Json.getArr? = .ok (r.base.spectrum.zipIdx.map SfsWire.encodeBin) := by
    rw [hb]
    rfl
  have hall : (r.base.spectrum.zipIdx.map SfsWire.encodeBin).all
      (fun b => (fieldsAllowed b binKeys).toOption.isSome) = true := by
    apply Array.all_eq_true.mpr
    intro i hi
    rw [Array.getElem_map, binFields_allowed]
    rfl
  unfold nullFieldsAllowed
  simp only [reportFields_allowed, ok_bind, hc, hm, hbins, coefficientFields_allowed,
    momentFields_allowed]
  rw [hall]
  rfl

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ r.base.valid = true ∧
      match r.inputCounts, r.observed with
      | none, none => True
      | some counts, some o =>
        counts.size = r.base.geneCopies - 1 ∧ o.counts.size = counts.size
      | _, _ => False := by
  rcases r with ⟨base, counts, obs⟩
  cases counts <;> cases obs <;> simp [Request.valid]

theorem Request.check_iff (r : Request) :
    r.check = true ↔ r.base.claim = Sfs.reportValues r.base.geneCopies r.base.theta ∧
      match r.inputCounts, r.observed with
      | none, none => True
      | some counts, some o =>
        o.counts = counts ∧ o.claim = SfsObserved.values r.base.geneCopies counts
      | _, _ => False := by
  rcases r with ⟨base, counts, obs⟩
  cases counts <;> cases obs <;>
    simp [Request.check, Sfs.checkReport_iff]

theorem Request.ofFormula_check (n : Nat) (theta : Rat) (counts : Option (Array Nat)) :
    (Request.ofFormula n theta counts).check = true := by
  cases counts <;>
    simp [Request.check_iff, Request.ofFormula, SfsWire.Request.ofFormula,
      SfsWire.Request.claim, Sfs.reportValues, Observed.ofCounts, Observed.claim,
      SfsObserved.values]

theorem Request.ofFormula_valid (n : Nat) (theta : Rat) (counts : Option (Array Nat))
    (hn : 2 ≤ n) (hu : n ≤ 4096) (ht : 0 ≤ theta)
    (hs : ∀ c, counts = some c → c.size = n - 1) :
    (Request.ofFormula n theta counts).valid = true := by
  cases counts with
  | none => simp [Request.valid, Request.ofFormula, SfsWire.Request.valid,
      SfsWire.Request.ofFormula, hn, hu, ht]
  | some c =>
    have hc := hs c rfl
    simp [Request.valid, Request.ofFormula, SfsWire.Request.valid,
      SfsWire.Request.ofFormula, Observed.ofCounts, hn, hu, ht, hc]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat × Nat,
      ([("schema", toJson "rhone-kernel-sfs-full-check-v1"),
        ("accepted", toJson d.1), ("checked_rational_values", toJson d.2.1),
        ("checked_observed_bins", toJson d.2.2),
        ("checker", toJson "Rhone.Computation.SfsFull.Request.check"),
        ("json_boundary_equality_proved", toJson false),
        ("rust_implementation_equality_proved", toJson false)] :
        List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    intro d
    simp
  have ha : ∀ d, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (hd d) (by simp [toJson])
  have hr : ∀ d, (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2.1 :=
    fun d => getNat_of (mkObj_getObjVal (hd d) (by simp))
  have hb : ∀ d, (stamp d).getObjValAs? Nat "checked_observed_bins" = .ok d.2.2 :=
    fun d => getNat_of (mkObj_getObjVal (hd d) (by simp))
  have h1 := ha first
  have h2 := hr first
  have h3 := hb first
  rw [h, ha second] at h1
  rw [h, hr second] at h2
  rw [h, hb second] at h3
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2 h3
  exact Prod.ext h1.symm (Prod.ext h2.symm h3.symm)

theorem requestAst_accept_sound (doc : Json) (rationalCount binCount : Nat)
    (haccept : requestAst doc = .ok (stamp (true, rationalCount, binCount))) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧ r.check = true ∧
      rationalCount = r.rationalCount ∧ binCount = r.binCount := by
  unfold requestAst decision at haccept
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at haccept
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at haccept
    | true =>
      have hs : stamp (r.check, r.rationalCount, r.binCount) =
          stamp (true, rationalCount, binCount) := by
        simpa [hdecode, hvalid, Except.map] using haccept
      have hp := stamp_injective hs
      simp only [Prod.mk.injEq] at hp
      exact ⟨r, rfl, hvalid, hp.1, hp.2.1.symm, hp.2.2.symm⟩

theorem Request.observed_sound (r : Request) (counts : Array Nat) (o : Observed)
    (hv : r.valid = true) (hc : r.check = true)
    (hi : r.inputCounts = some counts) (ho : r.observed = some o) :
    2 ≤ r.base.geneCopies ∧ r.base.geneCopies ≤ 4096 ∧ 0 ≤ r.base.theta ∧
      counts.size = r.base.geneCopies - 1 ∧ o.counts = counts ∧
      o.segregating = (SfsObserved.total counts : Rat) ∧
      o.watterson = Sfs.watterson r.base.geneCopies (SfsObserved.total counts) ∧
      o.pairwise = SfsObserved.pairwise r.base.geneCopies counts := by
  obtain ⟨hbase, hshape⟩ := (Request.valid_iff r).mp hv
  obtain ⟨hn, hu, ht⟩ := (SfsWire.Request.valid_iff r.base).mp hbase
  obtain ⟨_, hobs⟩ := (Request.check_iff r).mp hc
  rw [hi, ho] at hshape hobs
  have h0 := congrArg (fun a : Array Rat => a.getD 0 0) hobs.2
  have h1 := congrArg (fun a : Array Rat => a.getD 1 0) hobs.2
  have h2 := congrArg (fun a : Array Rat => a.getD 2 0) hobs.2
  refine ⟨hn, hu, ht, hshape.1, hobs.1, ?_, ?_, ?_⟩
  · simpa [Observed.claim, SfsObserved.values] using h0
  · simpa [Observed.claim, SfsObserved.values] using h1
  · simpa [Observed.claim, SfsObserved.values] using h2

theorem base_decode_encode (r : Request) :
    SfsWire.decode (encode r) = .ok r.base := by
  have hdq : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hdr : (reportFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [reportFields, SfsWire.reportFields]
  have hdc : (SfsWire.coefficientFields r.base).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [SfsWire.coefficientFields]
  have hdm : (SfsWire.momentFields r.base).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [SfsWire.momentFields]
  have hn := getNat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("gene_copies", toJson r.base.geneCopies) ∈ requestFields r))
  have htheta := rat_of (mkObj_getObjVal hdq (by simp [requestFields] :
    ("theta", Json.str (RationalWire.strictPrint r.base.theta)) ∈ requestFields r))
  have hreport := mkObj_getObjVal hdq (by simp [requestFields] :
    ("report", Json.mkObj (reportFields r)) ∈ requestFields r)
  have hschema := getStr_of (mkObj_getObjVal hdr (by
    simp [reportFields, SfsWire.reportFields, toJson] :
    ("schema", Json.str "rhone-sfs-v1") ∈ reportFields r))
  have hrn := getNat_of (mkObj_getObjVal hdr (by simp [reportFields, SfsWire.reportFields] :
    ("gene_copies", toJson r.base.geneCopies) ∈ reportFields r))
  have hrtheta := rat_of (mkObj_getObjVal hdr (by simp [reportFields, SfsWire.reportFields] :
    ("theta", Json.str (RationalWire.strictPrint r.base.theta)) ∈ reportFields r))
  have hcoefficients := mkObj_getObjVal hdr (by simp [reportFields, SfsWire.reportFields] :
    ("coefficients", Json.mkObj (SfsWire.coefficientFields r.base)) ∈ reportFields r)
  have hmoments := mkObj_getObjVal hdr (by simp [reportFields, SfsWire.reportFields] :
    ("null_moments", Json.mkObj (SfsWire.momentFields r.base)) ∈ reportFields r)
  have hspectrum := mkObj_getObjVal hdr (by simp [reportFields, SfsWire.reportFields] :
    ("expected_spectrum", Json.arr (r.base.spectrum.zipIdx.map SfsWire.encodeBin)) ∈ reportFields r)
  have ha1 := rat_of (mkObj_getObjVal hdc (by simp [SfsWire.coefficientFields] :
    ("a1", Json.str (RationalWire.strictPrint r.base.a1)) ∈ SfsWire.coefficientFields r.base))
  have ha2 := rat_of (mkObj_getObjVal hdc (by simp [SfsWire.coefficientFields] :
    ("a2", Json.str (RationalWire.strictPrint r.base.a2)) ∈ SfsWire.coefficientFields r.base))
  have hb1 := rat_of (mkObj_getObjVal hdc (by simp [SfsWire.coefficientFields] :
    ("b1", Json.str (RationalWire.strictPrint r.base.b1)) ∈ SfsWire.coefficientFields r.base))
  have hb2 := rat_of (mkObj_getObjVal hdc (by simp [SfsWire.coefficientFields] :
    ("b2", Json.str (RationalWire.strictPrint r.base.b2)) ∈ SfsWire.coefficientFields r.base))
  have hm1 := rat_of (mkObj_getObjVal hdm (by simp [SfsWire.momentFields] :
    ("mean_segregating", Json.str (RationalWire.strictPrint r.base.meanSegregating)) ∈
      SfsWire.momentFields r.base))
  have hm2 := rat_of (mkObj_getObjVal hdm (by simp [SfsWire.momentFields] :
    ("variance_segregating", Json.str (RationalWire.strictPrint r.base.varianceSegregating)) ∈
      SfsWire.momentFields r.base))
  have hm3 := rat_of (mkObj_getObjVal hdm (by simp [SfsWire.momentFields] :
    ("mean_pairwise", Json.str (RationalWire.strictPrint r.base.meanPairwise)) ∈
      SfsWire.momentFields r.base))
  have hm4 := rat_of (mkObj_getObjVal hdm (by simp [SfsWire.momentFields] :
    ("second_moment_pairwise", Json.str (RationalWire.strictPrint r.base.secondMomentPairwise)) ∈
      SfsWire.momentFields r.base))
  have hm5 := rat_of (mkObj_getObjVal hdm (by simp [SfsWire.momentFields] :
    ("variance_pairwise", Json.str (RationalWire.strictPrint r.base.variancePairwise)) ∈
      SfsWire.momentFields r.base))
  have hbins : ((Json.mkObj (reportFields r)).getObjVal? "expected_spectrum").bind
      Json.getArr? = .ok (r.base.spectrum.zipIdx.map SfsWire.encodeBin) := by
    rw [hspectrum]
    rfl
  simp only [encode] at *
  simp [SfsWire.decode, hn, htheta, hreport, hschema, hrn, hrtheta, hcoefficients, hmoments,
    ha1, ha2, hb1, hb2, hm1, hm2, hm3, hm4, hm5, hbins, SfsWire.bins_encode]

private theorem list_natArray (values : List Nat) :
    (values.map toJson).mapM Json.getNat? = (.ok values : Except String (List Nat)) := by
  have hnat : ∀ n : Nat, Json.getNat? (toJson n) = .ok n := fun _ => rfl
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, hnat, ih]

theorem natArray_encode (values : Array Nat) :
    natArray (.arr (values.map toJson)) = .ok values := by
  change (values.map toJson).mapM Json.getNat? = .ok values
  rw [Array.mapM_eq_mapM_toList]
  simp only [Array.toList_map]
  rw [list_natArray]
  simp

theorem observed_encode (o : Option Observed) : observed (encodeObserved o) = .ok o := by
  cases o with
  | none => rfl
  | some o =>
    have hd : (observedFields o).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
      simp [observedFields]
    have hc := mkObj_getObjVal hd (by simp [observedFields] :
      ("unfolded_counts", Json.arr (o.counts.map toJson)) ∈ observedFields o)
    have hs := rat_of (mkObj_getObjVal hd (by simp [observedFields] :
      ("segregating", Json.str (RationalWire.strictPrint o.segregating)) ∈ observedFields o))
    have hw := rat_of (mkObj_getObjVal hd (by simp [observedFields] :
      ("watterson", Json.str (RationalWire.strictPrint o.watterson)) ∈ observedFields o))
    have hp := rat_of (mkObj_getObjVal hd (by simp [observedFields] :
      ("pairwise", Json.str (RationalWire.strictPrint o.pairwise)) ∈ observedFields o))
    simp only [encodeObserved]
    unfold observed
    change (do
      fieldsAllowed (Json.mkObj (observedFields o)) observedKeys
      let counts ← ((Json.mkObj (observedFields o)).getObjVal? "unfolded_counts").bind natArray
      let segregating ← SfsWire.rat (Json.mkObj (observedFields o)) "segregating"
      let watterson ← SfsWire.rat (Json.mkObj (observedFields o)) "watterson"
      let pairwise ← SfsWire.rat (Json.mkObj (observedFields o)) "pairwise"
      pure (some (Observed.mk counts segregating watterson pairwise))) = .ok (some o)
    simp [observedFields_allowed, hc, hs, hw, hp, natArray_encode]

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hdq : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields]
  have hdr : (reportFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [reportFields, SfsWire.reportFields]
  have hreport := mkObj_getObjVal hdq (by simp [requestFields] :
    ("report", Json.mkObj (reportFields r)) ∈ requestFields r)
  have hop := getStr_of (mkObj_getObjVal hdq (by simp [requestFields, toJson] :
    ("op", Json.str "check_sfs") ∈ requestFields r))
  have hmodel := getStr_of (mkObj_getObjVal hdr (by simp [reportFields, toJson] :
    ("model", Json.str "kingman_constant_size_infinite_sites") ∈ reportFields r))
  have hmutation := getStr_of (mkObj_getObjVal hdr (by simp [reportFields, toJson] :
    ("mutation_rate_per_lineage", Json.str "theta/2") ∈ reportFields r))
  have hcoalescence := getStr_of (mkObj_getObjVal hdr (by simp [reportFields, toJson] :
    ("coalescence_rate_per_pair", Json.str "1/1") ∈ reportFields r))
  have hcounts := mkObj_getObjVal hdq (by
    simp [requestFields]
    rfl :
    ("counts", (match r.inputCounts with
      | none => Json.null
      | some c => Json.arr (c.map toJson))) ∈ requestFields r)
  have hobs := mkObj_getObjVal hdr (by simp [reportFields] :
    ("observed", encodeObserved r.observed) ∈ reportFields r)
  have hinput : inputCounts (optionalField (encode r) "counts") = .ok r.inputCounts := by
    simp only [encode] at *
    rw [optionalField, hcounts]
    cases r.inputCounts <;> simp [inputCounts, natArray_encode, Except.map]
  have hobserved : observed (optionalField (Json.mkObj (reportFields r)) "observed") =
      .ok r.observed := by
    rw [optionalField, hobs]
    exact observed_encode r.observed
  change (encode r).getObjVal? "report" = .ok (Json.mkObj (reportFields r)) at hreport
  change (encode r).getObjValAs? String "op" = .ok "check_sfs" at hop
  simp [decode, hop, base_decode_encode, hinput, hreport, hmodel, hmutation,
    hcoalescence, hobserved, nullFieldsAllowed_encode]

theorem requestAst_encode (r : Request) (hv : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.rationalCount, r.binCount)) := by
  simp [requestAst, decision, decode_encode, hv, Except.map]

theorem requestAst_encode_invalid (r : Request) (hv : r.valid = false) :
    requestAst (encode r) = .error "unsupported sample, theta, or observed count shape" := by
  simp [requestAst, decision, decode_encode, hv, Except.map]

theorem requestAst_ofFormula (n : Nat) (theta : Rat) (counts : Option (Array Nat))
    (hn : 2 ≤ n) (hu : n ≤ 4096) (ht : 0 ≤ theta)
    (hs : ∀ c, counts = some c → c.size = n - 1) :
    requestAst (encode (Request.ofFormula n theta counts)) =
      .ok (stamp (true, (Request.ofFormula n theta counts).rationalCount,
        (Request.ofFormula n theta counts).binCount)) := by
  rw [requestAst_encode _ (Request.ofFormula_valid n theta counts hn hu ht hs),
    Request.ofFormula_check]

theorem requestAst_accept_null_reader (doc : Json) (rationalCount binCount : Nat)
    (ha : requestAst doc = .ok (stamp (true, rationalCount, binCount))) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧ r.check = true ∧
      SfsWire.requestAst (SfsWire.encode r.base) =
        .ok (SfsWire.stamp (true, r.base.claim.size)) := by
  obtain ⟨r, hd, hv, hc, _, _⟩ := requestAst_accept_sound doc rationalCount binCount ha
  obtain ⟨hbase, _⟩ := (Request.valid_iff r).mp hv
  obtain ⟨hn, hu, ht⟩ := (SfsWire.Request.valid_iff r.base).mp hbase
  obtain ⟨hclaim, _⟩ := (Request.check_iff r).mp hc
  refine ⟨r, hd, hv, hc, ?_⟩
  rw [SfsWire.requestAst_encode r.base hn hu ht]
  rw [(Sfs.checkReport_iff _ _ _).mpr hclaim]

end Rhone.Computation.SfsFull
