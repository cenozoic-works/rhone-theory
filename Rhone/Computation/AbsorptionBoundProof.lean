/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.AbsorptionBound
public import Rhone.Computation.AbsorptionWireProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas

/-! # The absorption reader that compares the report with the inputs of the caller -/

@[expose] public section
namespace Rhone.Computation.AbsorptionBound
open Lean MarkovChain MeasureTheory

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

private theorem bind_ok {α β : Type} (x : α) (f : α → Except String β) :
    (Except.ok x : Except String α).bind f = f x := rfl

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

private theorem getBool_of {object : Json} {name : String} {value : Bool}
    (h : object.getObjVal? name = .ok (.bool value)) :
    object.getObjValAs? Bool name = .ok value := by
  change Json.getBool? ((object.getObjVal? name).toOption.getD .null) = _
  rw [h]
  rfl

private theorem rat_of {object : Json} {name : String} {value : Rat}
    (h : object.getObjVal? name = .ok (AbsorptionWire.encodeEntry value)) :
    AbsorptionWire.rat object name = .ok value := by
  rw [AbsorptionWire.rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => simp at h
  | ok a => exact step a rfl h

theorem Request.bound_iff (r : Request) :
    r.bound = true ↔ r.report.moran = r.inputs.moran ∧
      r.report.geneCopies = r.inputs.geneCopies ∧
      r.report.initialCount = r.inputs.initialCount ∧
      r.report.fitness = r.inputs.fitness ∧ r.report.provenance = r.inputs.provenance := by
  unfold Request.bound
  rw [decide_eq_true_iff]

private theorem stamp_fields (d : Bool × Nat × Bool) :
    ([("schema", toJson "rhone-compute-absorption-bound-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2.1),
      ("inputs_match", toJson d.2.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have ha : ∀ d : Bool × Nat × Bool, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hc : ∀ d : Bool × Nat × Bool,
      (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2.1 :=
    fun d => getNat_of (mkObj_getObjVal (stamp_fields d) (by simp))
  have hb : ∀ d : Bool × Nat × Bool,
      (stamp d).getObjVal? "inputs_match" = .ok (.bool d.2.2) :=
    fun d => mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have h1 := ha first
  have h2 := hc first
  have h3 := hb first
  rw [h] at h1 h2 h3
  rw [ha second] at h1
  rw [hc second] at h2
  rw [hb second] at h3
  obtain ⟨a1, c1, b1⟩ := first
  obtain ⟨a2, c2, b2⟩ := second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2 h3
  simp [h1, h2, h3]

theorem stamp_ne_wire_stamp (d : Bool × Nat × Bool) (e : Bool × Nat) :
    stamp d ≠ AbsorptionWire.stamp e := by
  intro h
  have h1 : (stamp d).getObjVal? "schema" =
      .ok (.str "rhone-compute-absorption-bound-check-v1") :=
    mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hfields : ([("schema", toJson "rhone-compute-absorption-check-v1"),
      ("accepted", toJson e.1), ("checked_rational_values", toJson e.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp
  have h2 : (AbsorptionWire.stamp e).getObjVal? "schema" =
      .ok (.str "rhone-compute-absorption-check-v1") :=
    mkObj_getObjVal hfields (by simp [toJson])
  rw [h, h2] at h1
  simp at h1

theorem decode_report (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    ∃ report : Json, doc.getObjVal? "report" = .ok report ∧
      AbsorptionWire.decode report = .ok r.report := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun inputs _ h => ?_
  refine of_bind_ok h fun report hreport h => ?_
  obtain rfl := Except.ok.inj h
  cases hvalue : doc.getObjVal? "report" with
  | error e =>
    rw [hvalue] at hreport
    change Except.error e = _ at hreport
    cases hreport
  | ok value =>
    rw [hvalue] at hreport
    exact ⟨value, rfl, hreport⟩

private theorem requestFields_pairwise (r : Request) :
    (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp [requestFields]

private theorem inputModel_encode (r : Request)
    (hinputs : r.inputs.moran = false → r.inputs.fitness = 1) :
    inputModel (encode r) (if r.inputs.moran then "moran" else "wright-fisher") =
      .ok (r.inputs.moran, r.inputs.fitness) := by
  obtain ⟨⟨moran, n, i, fitness, provenance⟩, report⟩ := r
  cases moran with
  | false =>
    have hone : fitness = 1 := hinputs rfl
    subst hone
    have hfitness : (encode ⟨⟨false, n, i, 1, provenance⟩, report⟩).getObjVal?
        "relative_fitness" = .ok .null :=
      mkObj_getObjVal (requestFields_pairwise _) (by simp [requestFields])
    simp [inputModel, hfitness, wfFitness, Except.bind]
  | true =>
    have hfitness := rat_of (mkObj_getObjVal
      (requestFields_pairwise ⟨⟨true, n, i, fitness, provenance⟩, report⟩)
      (by simp [requestFields] :
        ("relative_fitness", AbsorptionWire.encodeEntry fitness) ∈
          requestFields ⟨⟨true, n, i, fitness, provenance⟩, report⟩))
    simp only [encode] at *
    simp [inputModel, hfitness, Except.map]

theorem decode_encode (r : Request) (hinputs : r.inputs.moran = false → r.inputs.fitness = 1)
    (hreport : r.report.Canonical) : decode (encode r) = .ok r := by
  have hd := requestFields_pairwise r
  have hfields := inputModel_encode r hinputs
  have hvalue : (encode r).getObjVal? "report" = .ok (AbsorptionWire.encode r.report) :=
    mkObj_getObjVal hd (by simp [requestFields] :
      ("report", AbsorptionWire.encode r.report) ∈ requestFields r)
  have hin : decodeInputs (encode r) = .ok r.inputs := by
    have hmodel := getStr_of (mkObj_getObjVal hd (by simp [requestFields] :
      ("model", Json.str (if r.inputs.moran then "moran" else "wright-fisher")) ∈
        requestFields r))
    have hn := getNat_of (mkObj_getObjVal hd (by simp [requestFields] :
      ("gene_copies", toJson r.inputs.geneCopies) ∈ requestFields r))
    have hi := getNat_of (mkObj_getObjVal hd (by simp [requestFields] :
      ("initial_count", toJson r.inputs.initialCount) ∈ requestFields r))
    have hprov := getStr_of (mkObj_getObjVal hd (by simp [requestFields] :
      ("parameter_provenance", Json.str r.inputs.provenance) ∈ requestFields r))
    have henc : encode r = Json.mkObj (requestFields r) := rfl
    rw [henc] at hfields ⊢
    unfold decodeInputs
    rw [hmodel, ok_bind, hn, ok_bind, hi, ok_bind, hprov, ok_bind, hfields, ok_bind]
    rfl
  unfold decode
  rw [hin, ok_bind, hvalue, bind_ok, AbsorptionWire.decode_encode r.report hreport, ok_bind]
  rfl

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.report.valid = true ∧
      out = stamp (r.bound && r.report.check, r.report.claimed, r.bound) := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.report.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      refine ⟨r, rfl, hvalid, ?_⟩
      simpa [hdecode, hvalid, Except.map] using hok.symm

theorem decision_wire (doc : Json) (d : Bool × Nat × Bool) (h : decision doc = .ok d) :
    ∃ report : Json, doc.getObjVal? "report" = .ok report ∧
      ∃ accepted : Bool, AbsorptionWire.decision report = .ok (accepted, d.2.1) ∧
        d.1 = (d.2.2 && accepted) := by
  unfold decision at h
  cases hdecode : decode doc with
  | error message => simp [hdecode] at h
  | ok r =>
    cases hvalid : r.report.valid with
    | false => simp [hdecode, hvalid] at h
    | true =>
      have hd : d = (r.bound && r.report.check, r.report.claimed, r.bound) := by
        simpa [hdecode, hvalid] using h.symm
      obtain ⟨report, hfield, hreport⟩ := decode_report doc r hdecode
      refine ⟨report, hfield, r.report.check, ?_, ?_⟩
      · simp [AbsorptionWire.decision, hreport, hvalid, hd]
      · simp [hd]

theorem requestAst_mismatch (doc out : Json) (r : Request) (hok : requestAst doc = .ok out)
    (hdecode : decode doc = .ok r) (hbound : r.bound = false) :
    out = stamp (false, r.report.claimed, false) := by
  obtain ⟨decoded, hdecoded, -, hout⟩ := requestAst_ok doc out hok
  rw [hdecode] at hdecoded
  obtain rfl := Except.ok.inj hdecoded
  rw [hout, hbound]
  rfl

theorem requestAst_accept_sound (doc : Json) (count : Nat) (flag : Bool)
    (haccept : requestAst doc = .ok (stamp (true, count, flag))) :
    ∃ r : Request, decode doc = .ok r ∧ flag = true ∧
      r.report.moran = r.inputs.moran ∧ r.report.geneCopies = r.inputs.geneCopies ∧
      r.report.initialCount = r.inputs.initialCount ∧
      r.report.fitness = r.inputs.fitness ∧ r.report.provenance = r.inputs.provenance ∧
      r.report.valid = true ∧ r.report.check = true ∧ count = r.report.claimed ∧
      ∃ report : Json, doc.getObjVal? "report" = .ok report ∧
        AbsorptionWire.requestAst report = .ok (AbsorptionWire.stamp (true, count)) := by
  obtain ⟨r, hdecode, hvalid, hout⟩ := requestAst_ok doc _ haccept
  have htriple := stamp_injective hout
  simp only [Prod.mk.injEq] at htriple
  obtain ⟨hboth, hcount, hflag⟩ := htriple
  have hboth' : (r.bound && r.report.check) = true := hboth.symm
  rw [Bool.and_eq_true] at hboth'
  obtain ⟨hbound, hcheck⟩ := hboth'
  obtain ⟨h1, h2, h3, h4, h5⟩ := (Request.bound_iff r).mp hbound
  obtain ⟨report, hfield, hreport⟩ := decode_report doc r hdecode
  refine ⟨r, hdecode, hflag.trans hbound, h1, h2, h3, h4, h5, hvalid, hcheck, hcount,
    report, hfield, ?_⟩
  simp [AbsorptionWire.requestAst, AbsorptionWire.decision, hreport, hvalid, hcheck, hcount,
    Except.map]

theorem requestAst_accept_hitTime (doc : Json) (count : Nat) (flag : Bool)
    (haccept : requestAst doc = .ok (stamp (true, count, flag))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 < r.inputs.geneCopies ∧
      ∀ x : Fin (r.inputs.geneCopies + 1), (x : Nat) = r.inputs.initialCount →
        (r.inputs.moran = false →
          ∫⁻ ω, (hitTime (fixationBoundary r.inputs.geneCopies) ω : ENNReal)
            ∂(wfChain r.inputs.geneCopies).pathLaw x =
              ENNReal.ofReal (r.report.scalar : Real)) ∧
        (r.inputs.moran = true → ∃ hr : 0 < (r.inputs.fitness : Real),
          ∫⁻ ω, (hitTime (fixationBoundary r.inputs.geneCopies) ω : ENNReal)
            ∂(moranChain r.inputs.geneCopies (r.inputs.fitness : Real) hr).pathLaw x =
              ENNReal.ofReal (r.report.scalar : Real)) := by
  obtain ⟨r, hdecode, -, h1, h2, h3, h4, -, hvalid, -, -, report, hfield, hwire⟩ :=
    requestAst_accept_sound doc count flag haccept
  obtain ⟨decoded, hdecoded, hpos, hwf, hmoran⟩ :=
    AbsorptionWire.requestAst_accept_hitTime report count hwire
  obtain ⟨report', hfield', hreport'⟩ := decode_report doc r hdecode
  obtain ⟨-, -, -, -, -, hscalar⟩ := (AbsorptionWire.Request.valid_iff r.report).mp hvalid
  obtain rfl : report = report' := Except.ok.inj (hfield.symm.trans hfield')
  have hsame : decoded = r.report := Except.ok.inj (hdecoded.symm.trans hreport')
  subst hsame
  obtain ⟨⟨im, n, i, f, p⟩, ⟨rm, rn, ri, rf, rp, rk, rt, rs⟩⟩ := r
  dsimp only at h1 h2 h3 h4 hpos hwf hmoran hscalar ⊢
  subst h1 h2 h3 h4
  refine ⟨_, hdecode, hpos, ?_⟩
  dsimp only
  intro x hx
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rw [hscalar, ← hx]
    exact hwf hm x
  · obtain ⟨hr, hall⟩ := hmoran hm
    refine ⟨hr, ?_⟩
    rw [hscalar, ← hx]
    exact hall x

end Rhone.Computation.AbsorptionBound
