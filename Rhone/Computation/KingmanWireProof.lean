/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.KingmanWire
public import Rhone.Computation.KingmanAcceptanceProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the Kingman genealogy-moments report reader -/

@[expose] public section
namespace Rhone.Computation.KingmanWire
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

private theorem strictRat_strictPrint (value : Rat) :
    strictRat (RationalWire.strictPrint value) = .ok value := by
  simp [strictRat, RationalWire.decode_strictPrint]

private theorem rat_of {object : Json} {name : String} {value : Rat}
    (h : object.getObjVal? name = .ok (encodeRat value)) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  exact strictRat_strictPrint value

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value :=
  mkObj_getObjVal (by simp [requestFields]) hmem

private theorem moments_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ momentFields r) :
    (Json.mkObj (momentFields r)).getObjVal? name = .ok value :=
  mkObj_getObjVal (by simp [momentFields]) hmem

private theorem moments_size (r : Request) :
    (Json.mkObj (momentFields r)).getObj? =
      .ok (Std.TreeMap.Raw.ofList (momentFields r) compare) := rfl

private theorem moments_size_eq (r : Request) :
    (Std.TreeMap.Raw.ofList (momentFields r) compare).size = 4 := by
  simp [momentFields, Std.TreeMap.Raw.size_ofList]

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ 1 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ r.pairRate = 1 := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem Request.claim_ofFormula (n : Nat) (unit : String) :
    (Request.ofFormula n unit).claim = Kingman.reportValues n := rfl

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-kingman-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false),
      ("supplied_rate_scaling_proved", toJson false)] :
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

theorem decode_encode (r : Request) (hcanonical : r.Canonical) :
    decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-genealogy-moments-v1") (by simp [requestFields, toJson]))
  have hmodel := getStr_of (encode_getObjVal (r := r) (name := "model")
    (value := .str "supplied_neutral_constant_size_kingman")
    (by simp [requestFields, toJson]))
  have hconvention := getStr_of (encode_getObjVal (r := r) (name := "rate_convention")
    (value := .str "each_unordered_pair_has_supplied_rate_per_time_unit")
    (by simp [requestFields, toJson]))
  have hn := getNat_of (encode_getObjVal (r := r) (name := "gene_copies")
    (value := toJson r.geneCopies) (by simp [requestFields]))
  have hrate := rat_of (encode_getObjVal (r := r) (name := "pair_rate_per_unit")
    (value := encodeRat r.pairRate) (by simp [requestFields]))
  have hunit := getStr_of (encode_getObjVal (r := r) (name := "time_unit")
    (value := .str r.timeUnit) (by simp [requestFields]))
  have hcheck : checkUnit r.timeUnit = .ok r.timeUnit := by
    have : unitOk r.timeUnit = true := hcanonical
    simp [checkUnit, this]
  have hbind : (Except.ok r.timeUnit : Except String String).bind checkUnit =
      .ok r.timeUnit := hcheck
  have hvalues := encode_getObjVal (r := r) (name := "moments")
    (value := Json.mkObj (momentFields r)) (by simp [requestFields])
  have h1 := rat_of (moments_getObjVal (r := r) (name := "mean_tmrca")
    (value := encodeRat r.meanTmrca) (by simp [momentFields]))
  have h2 := rat_of (moments_getObjVal (r := r) (name := "variance_tmrca")
    (value := encodeRat r.varianceTmrca) (by simp [momentFields]))
  have h3 := rat_of (moments_getObjVal (r := r) (name := "mean_total_branch_length")
    (value := encodeRat r.meanTotalBranchLength) (by simp [momentFields]))
  have h4 := rat_of (moments_getObjVal (r := r) (name := "variance_total_branch_length")
    (value := encodeRat r.varianceTotalBranchLength) (by simp [momentFields]))
  simp [decode, hschema, hmodel, hconvention, hn, hrate, hunit, hbind, hvalues,
    moments_size, moments_size_eq, h1, h2, h3, h4]

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => simp at h
  | ok a => exact step a rfl h

private theorem of_guard_ok {β : Type} {c : Prop} [Decidable c] {e : String}
    {k : Unit → Except String β} {b : β}
    (h : (if c then (throw e >>= fun r => k r) else k ()) = .ok b) : k () = .ok b := by
  split at h
  · simp at h
  · exact h

private theorem checkUnit_ok {unit value : String} (h : checkUnit unit = .ok value) :
    unitOk value = true := by
  unfold checkUnit at h
  split at h
  · obtain rfl := Except.ok.inj h
    assumption
  · simp at h

theorem decode_canonical (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    r.Canonical := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun schema _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun model _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun convention _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun n _ h => ?_
  refine of_bind_ok h fun rate _ h => ?_
  refine of_bind_ok h fun unit hunit h => ?_
  refine of_bind_ok h fun values _ h => ?_
  refine of_bind_ok h fun fields _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun a _ h => ?_
  refine of_bind_ok h fun b _ h => ?_
  refine of_bind_ok h fun c _ h => ?_
  refine of_bind_ok h fun d _ h => ?_
  obtain rfl := Except.ok.inj h
  refine of_bind_ok (x := (doc.getObjValAs? String "time_unit")) (f := checkUnit)
    (b := unit) (P := _) ?_ fun label _ hcheck => ?_
  · exact hunit
  · exact checkUnit_ok hcheck

private theorem decision_encode (r : Request) (hcanonical : r.Canonical) :
    decision (encode r) = if r.valid then .ok (Kingman.checkReport r.geneCopies r.claim,
      r.claim.size) else .error "unsupported sample size or pair rate" := by
  simp [decision, decode_encode r hcanonical]

theorem requestAst_encode (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = true) :
    requestAst (encode r) =
      .ok (stamp (Kingman.checkReport r.geneCopies r.claim, r.claim.size)) := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported sample size or pair rate" := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      out = stamp (Kingman.checkReport r.geneCopies r.claim, r.claim.size) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    have hcanonical := decode_canonical doc r hdecode
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (Kingman.checkReport r.geneCopies r.claim, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hcanonical, hvalid, hout, hout ▸ requestAst_encode r hcanonical hvalid⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      r.claim = Kingman.reportValues r.geneCopies ∧ count = r.claim.size ∧
      requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hcanonical, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  exact ⟨r, hdecode, hcanonical, hvalid, (Kingman.checkReport_iff _ _).mp hpair.1.symm,
    hpair.2, hencode⟩

theorem requestAst_encode_accept_sound (r : Request) (hcanonical : r.Canonical)
    (count : Nat) (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    r.valid = true ∧ r.claim = Kingman.reportValues r.geneCopies ∧ count = r.claim.size := by
  obtain ⟨decoded, hdecode, -, hvalid, hclaim, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode r hcanonical] at hdecode
  cases hdecode
  exact ⟨hvalid, hclaim, hcount⟩

theorem requestAst_accept_request (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      (⟨r.geneCopies, r.pairRate⟩ : Kingman.Request).valid = true ∧
      (⟨r.geneCopies, r.pairRate⟩ : Kingman.Request).check r.claim = true := by
  obtain ⟨r, hdecode, -, hvalid, hclaim, -, -⟩ := requestAst_accept_sound doc count haccept
  refine ⟨r, hdecode, (Kingman.Request.valid_iff _).mpr ((Request.valid_iff r).mp hvalid), ?_⟩
  exact (Kingman.checkReport_iff _ _).mpr hclaim

theorem requestAst_ofFormula (n : Nat) (unit : String) (hunit : unitOk unit = true)
    (hlower : 1 ≤ n) (hupper : n ≤ 4096) :
    requestAst (encode (Request.ofFormula n unit)) =
      .ok (stamp (true, (Kingman.reportValues n).size)) := by
  have hcanonical : (Request.ofFormula n unit).Canonical := hunit
  have hvalid : (Request.ofFormula n unit).valid = true :=
    (Request.valid_iff _).mpr ⟨hlower, hupper, rfl⟩
  have hclaim : (Request.ofFormula n unit).claim = Kingman.reportValues n := rfl
  rw [requestAst_encode _ hcanonical hvalid]
  change Except.ok (stamp (Kingman.checkReport n (Request.ofFormula n unit).claim,
    (Request.ofFormula n unit).claim.size)) = _
  rw [hclaim, Kingman.checkReport_complete]

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.KingmanWire
