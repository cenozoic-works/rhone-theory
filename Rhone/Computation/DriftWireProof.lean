/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftWire
public import Rhone.Computation.DriftAcceptanceProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the drift report reader -/

@[expose] public section
namespace Rhone.Computation.DriftWire
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

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value :=
  mkObj_getObjVal (by simp [requestFields]) hmem

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ 1 ≤ r.geneCopies ∧ r.geneCopies ≤ 64 ∧ r.initialCount ≤ r.geneCopies ∧
      r.steps ≤ 256 ∧ (r.moran = true → 0 < r.fitness) := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat × Bool, ([("schema", toJson "rhone-compute-drift-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2.1),
      ("neutral_heterozygosity_checked", toJson d.2.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    intro d
    simp
  have ha : ∀ d : Bool × Nat × Bool, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (hd d) (by simp [toJson])
  have hc : ∀ d : Bool × Nat × Bool,
      (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2.1 :=
    fun d => getNat_of (mkObj_getObjVal (hd d) (by simp))
  have hf : ∀ d : Bool × Nat × Bool,
      (stamp d).getObjVal? "neutral_heterozygosity_checked" = .ok (.bool d.2.2) :=
    fun d => mkObj_getObjVal (hd d) (by simp [toJson])
  have h1 := ha first
  have h2 := hc first
  have h3 := hf first
  rw [h] at h1 h2 h3
  rw [ha second] at h1
  rw [hc second] at h2
  rw [hf second] at h3
  obtain ⟨a, c, f⟩ := first
  obtain ⟨a', c', f'⟩ := second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2 h3
  simp [h1, h2, h3]

private theorem rowEntry_encodeEntry (value : Rat) :
    rowEntry (encodeEntry value) = .ok value :=
  RationalWire.decode_strictPrint value

private theorem list_row_encode (values : List Rat) :
    (values.map encodeEntry).mapM rowEntry = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, rowEntry_encodeEntry, ih]

theorem row_encode (values : Array Rat) :
    (values.map encodeEntry).mapM rowEntry = .ok values := by
  have hl := list_row_encode values.toList
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

private theorem modelFields_encode (r : Request) (hcanonical : r.Canonical) :
    modelFields (encode r) (if r.moran then "moran" else "wright-fisher") =
      .ok (r.moran, r.fitness) := by
  obtain ⟨moran, n, i, t, fitness, row, fixation, heterozygosity⟩ := r
  cases moran with
  | false =>
    have hone : fitness = 1 := hcanonical.1 rfl
    subst hone
    have hfitness := encode_getObjVal (r := ⟨false, n, i, t, 1, row, fixation,
      heterozygosity⟩) (name := "relative_fitness") (value := .null) (by simp [requestFields])
    have hunit := getStr_of (encode_getObjVal (r := ⟨false, n, i, t, 1, row, fixation,
      heterozygosity⟩) (name := "time_unit") (value := .str "generation")
      (by simp [requestFields]))
    simp [modelFields, hfitness, hunit]
  | true =>
    have hfitness := rat_of (encode_getObjVal (r := ⟨true, n, i, t, fitness, row, fixation,
      heterozygosity⟩) (name := "relative_fitness") (value := encodeEntry fitness)
      (by simp [requestFields]))
    have hunit := getStr_of (encode_getObjVal (r := ⟨true, n, i, t, fitness, row, fixation,
      heterozygosity⟩) (name := "time_unit") (value := .str "birth-death-event")
      (by simp [requestFields]))
    simp [modelFields, hfitness, hunit]

private theorem heterozygosityField_encode (r : Request) (hcanonical : r.Canonical) :
    heterozygosityField (encode r) r.neutral = .ok r.heterozygosity := by
  obtain ⟨moran, n, i, t, fitness, row, fixation, heterozygosity⟩ := r
  have hshape := hcanonical.2
  cases heterozygosity with
  | none =>
    simp only [Option.isSome_none] at hshape
    simp [heterozygosityField, ← hshape]
  | some value =>
    simp only [Option.isSome_some] at hshape
    have hvalue := rat_of (encode_getObjVal (r := ⟨moran, n, i, t, fitness, row, fixation,
      some value⟩) (name := "expected_heterozygosity") (value := encodeEntry value)
      (by simp [requestFields]))
    simp [heterozygosityField, ← hshape, hvalue, Except.map]

theorem decode_encode (r : Request) (hcanonical : r.Canonical) :
    decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-drift-v1") (by simp [requestFields, toJson]))
  have hsemantics := getStr_of (encode_getObjVal (r := r) (name := "comparison_semantics")
    (value := .str "exact_fraction") (by simp [requestFields, toJson]))
  have hmodel := getStr_of (encode_getObjVal (r := r) (name := "model")
    (value := .str (if r.moran then "moran" else "wright-fisher")) (by simp [requestFields]))
  have hn := getNat_of (encode_getObjVal (r := r) (name := "gene_copies")
    (value := toJson r.geneCopies) (by simp [requestFields]))
  have hi := getNat_of (encode_getObjVal (r := r) (name := "initial_count")
    (value := toJson r.initialCount) (by simp [requestFields]))
  have ht := getNat_of (encode_getObjVal (r := r) (name := "steps")
    (value := toJson r.steps) (by simp [requestFields]))
  have hsampling := getStr_of (encode_getObjVal (r := r) (name := "heterozygosity_sampling")
    (value := .str "with-replacement") (by simp [requestFields, toJson]))
  have hrow : ((encode r).getObjVal? "transition_row").bind Json.getArr? =
      .ok (r.row.map encodeEntry) := by
    rw [encode_getObjVal (r := r) (name := "transition_row")
      (value := .arr (r.row.map encodeEntry)) (by simp [requestFields])]
    rfl
  have hfixation := rat_of (encode_getObjVal (r := r) (name := "fixation_probability")
    (value := encodeEntry r.fixation) (by simp [requestFields]))
  have hfields := modelFields_encode r hcanonical
  have hheterozygosity := heterozygosityField_encode r hcanonical
  simp only [Request.neutral] at hheterozygosity
  have hentries : r.row.mapM (rowEntry ∘ encodeEntry) = .ok r.row := by
    simpa using row_encode r.row
  simp [decode, hschema, hsemantics, hmodel, hn, hi, ht, hsampling, hrow, hentries,
    hfixation, hfields, hheterozygosity]

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

private theorem modelFields_fitness (doc : Json) (model : String) (fields : Bool × Rat)
    (h : modelFields doc model = .ok fields) : fields.1 = false → fields.2 = 1 := by
  unfold modelFields at h
  split at h
  · refine of_bind_ok h fun fitness _ h => ?_
    split at h
    · refine of_bind_ok h fun timeUnit _ h => ?_
      replace h := of_guard_ok h
      obtain rfl := Except.ok.inj h
      intro _
      rfl
    · simp at h
  · split at h
    · refine of_bind_ok h fun timeUnit _ h => ?_
      replace h := of_guard_ok h
      refine of_bind_ok h fun fitness _ h => ?_
      obtain rfl := Except.ok.inj h
      intro hmodel
      cases hmodel
    · simp at h

private theorem heterozygosityField_isSome (doc : Json) (neutral : Bool)
    (value : Option Rat) (h : heterozygosityField doc neutral = .ok value) :
    value.isSome = neutral := by
  cases neutral with
  | false =>
    obtain rfl : none = value := by simpa [heterozygosityField] using h
    rfl
  | true =>
    cases hfield : rat doc "expected_heterozygosity" with
    | error e => simp [heterozygosityField, hfield, Except.map] at h
    | ok found =>
      obtain rfl : some found = value := by
        simpa [heterozygosityField, hfield, Except.map] using h
      rfl

theorem decode_canonical (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    r.Canonical := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun schema _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun semantics _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun model _ h => ?_
  refine of_bind_ok h fun n _ h => ?_
  refine of_bind_ok h fun i _ h => ?_
  refine of_bind_ok h fun t _ h => ?_
  refine of_bind_ok h fun fields hfields h => ?_
  refine of_bind_ok h fun sampling _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun entries _ h => ?_
  refine of_bind_ok h fun row _ h => ?_
  refine of_bind_ok h fun fixation _ h => ?_
  refine of_bind_ok h fun heterozygosity hvalue h => ?_
  obtain rfl := Except.ok.inj h
  exact ⟨modelFields_fitness doc model fields hfields,
    heterozygosityField_isSome doc _ _ hvalue⟩

private theorem decision_encode (r : Request) (hcanonical : r.Canonical) :
    decision (encode r) = if r.valid then .ok (r.check, r.claim.size, r.neutral)
      else .error "unsupported drift request domain" := by
  simp [decision, decode_encode r hcanonical]

theorem requestAst_encode (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.claim.size, r.neutral)) := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported drift request domain" := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      out = stamp (r.check, r.claim.size, r.neutral) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    have hcanonical := decode_canonical doc r hdecode
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, r.claim.size, r.neutral) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hcanonical, hvalid, hout, hout ▸ requestAst_encode r hcanonical hvalid⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat) (neutral : Bool)
    (haccept : requestAst doc = .ok (stamp (true, count, neutral))) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      (r.moran = false →
        r.claim = Drift.wfReportValues r.geneCopies r.initialCount r.steps) ∧
      (r.moran = true →
        r.claim = Drift.moranReportValues r.geneCopies r.fitness r.initialCount r.steps) ∧
      count = r.claim.size ∧ neutral = r.neutral ∧
      requestAst (encode r) = .ok (stamp (true, count, neutral)) := by
  obtain ⟨r, hdecode, hcanonical, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have htriple := stamp_injective hout
  simp only [Prod.mk.injEq] at htriple
  obtain ⟨hcheck, hcount, hneutral⟩ := htriple
  refine ⟨r, hdecode, hcanonical, hvalid, ?_, ?_, hcount, hneutral, hencode⟩
  · intro hmodel
    have hwf : Drift.checkWfReport r.geneCopies r.initialCount r.steps r.claim = true := by
      simpa [Request.check, hmodel] using hcheck.symm
    exact (Drift.checkWfReport_iff _ _ _ _).mp hwf
  · intro hmodel
    have hmoran : Drift.checkMoranReport r.geneCopies r.fitness r.initialCount r.steps
        r.claim = true := by
      simpa [Request.check, hmodel] using hcheck.symm
    exact (Drift.checkMoranReport_iff _ _ _ _ _).mp hmoran

theorem requestAst_encode_accept_sound (r : Request) (hcanonical : r.Canonical)
    (count : Nat) (neutral : Bool)
    (haccept : requestAst (encode r) = .ok (stamp (true, count, neutral))) :
    r.valid = true ∧
      (r.moran = false →
        r.claim = Drift.wfReportValues r.geneCopies r.initialCount r.steps) ∧
      (r.moran = true →
        r.claim = Drift.moranReportValues r.geneCopies r.fitness r.initialCount r.steps) ∧
      count = r.claim.size ∧ neutral = r.neutral := by
  obtain ⟨decoded, hdecode, -, hvalid, hwf, hmoran, hcount, hneutral, -⟩ :=
    requestAst_accept_sound (encode r) count neutral haccept
  rw [decode_encode r hcanonical] at hdecode
  cases hdecode
  exact ⟨hvalid, hwf, hmoran, hcount, hneutral⟩

theorem requestAst_accept_request (doc : Json) (count : Nat) (neutral : Bool)
    (haccept : requestAst doc = .ok (stamp (true, count, neutral))) :
    ∃ r : Request, decode doc = .ok r ∧
      (r.moran = false →
        (⟨r.geneCopies, r.initialCount, r.steps⟩ : Drift.WfRequest).valid = true ∧
        (⟨r.geneCopies, r.initialCount, r.steps⟩ : Drift.WfRequest).check r.claim = true) ∧
      (r.moran = true →
        (⟨r.geneCopies, r.fitness, r.initialCount, r.steps⟩ : Drift.MoranRequest).valid
          = true ∧
        (⟨r.geneCopies, r.fitness, r.initialCount, r.steps⟩ : Drift.MoranRequest).check
          r.claim = true) := by
  obtain ⟨r, hdecode, -, hvalid, hwf, hmoran, -, -, -⟩ :=
    requestAst_accept_sound doc count neutral haccept
  obtain ⟨hlower, hupper, hinitial, hsteps, hfitness⟩ := (Request.valid_iff r).mp hvalid
  refine ⟨r, hdecode, ?_, ?_⟩
  · intro hmodel
    exact ⟨(Drift.WfRequest.valid_iff _).mpr ⟨hlower, hupper, hinitial, hsteps⟩,
      (Drift.checkWfReport_iff _ _ _ _).mpr (hwf hmodel)⟩
  · intro hmodel
    exact ⟨(Drift.MoranRequest.valid_iff _).mpr
        ⟨hlower, hupper, hinitial, hsteps, hfitness hmodel⟩,
      (Drift.checkMoranReport_iff _ _ _ _ _).mpr (hmoran hmodel)⟩

theorem requestAst_wfFormula (n i t : Nat) (hlower : 1 ≤ n) (hupper : n ≤ 64)
    (hinitial : i ≤ n) (hsteps : t ≤ 256) :
    requestAst (encode (Request.wfFormula n i t)) =
      .ok (stamp (true, (Drift.wfReportValues n i t).size, true)) := by
  have hcanonical : (Request.wfFormula n i t).Canonical := by
    simp [Request.Canonical, Request.wfFormula, Request.neutral]
  have hvalid : (Request.wfFormula n i t).valid = true :=
    (Request.valid_iff _).mpr ⟨hlower, hupper, hinitial, hsteps, by simp [Request.wfFormula]⟩
  have hclaim : (Request.wfFormula n i t).claim = Drift.wfReportValues n i t := by
    apply Array.ext'
    simp [Request.claim, Request.wfFormula, Drift.wfReportValues]
  have hcheck : (Request.wfFormula n i t).check = true := by
    unfold Request.check
    rw [hclaim]
    simpa [Request.wfFormula] using Drift.checkWfReport_complete n i t
  have hneutral : (Request.wfFormula n i t).neutral = true := rfl
  rw [requestAst_encode _ hcanonical hvalid, hcheck, hclaim, hneutral]

theorem requestAst_moranFormula (n : Nat) (fitness : Rat) (i t : Nat) (hlower : 1 ≤ n)
    (hupper : n ≤ 64) (hinitial : i ≤ n) (hsteps : t ≤ 256) (hfitness : 0 < fitness) :
    requestAst (encode (Request.moranFormula n fitness i t)) =
      .ok (stamp (true, (Drift.moranReportValues n fitness i t).size,
        decide (fitness = 1))) := by
  have hcanonical : (Request.moranFormula n fitness i t).Canonical := by
    by_cases hone : fitness = 1 <;>
      simp [Request.Canonical, Request.moranFormula, Request.neutral, hone]
  have hvalid : (Request.moranFormula n fitness i t).valid = true :=
    (Request.valid_iff _).mpr ⟨hlower, hupper, hinitial, hsteps, fun _ => hfitness⟩
  have hclaim : (Request.moranFormula n fitness i t).claim =
      Drift.moranReportValues n fitness i t := by
    by_cases hone : fitness = 1 <;>
      simp [Request.claim, Request.moranFormula, Drift.moranReportValues, hone]
  have hcheck : (Request.moranFormula n fitness i t).check = true := by
    unfold Request.check
    rw [hclaim]
    simpa [Request.moranFormula] using Drift.checkMoranReport_complete n fitness i t
  have hneutral : (Request.moranFormula n fitness i t).neutral = decide (fitness = 1) := by
    by_cases hone : fitness = 1 <;> simp [Request.neutral, Request.moranFormula, hone]
  rw [requestAst_encode _ hcanonical hvalid, hcheck, hclaim, hneutral]

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.DriftWire
