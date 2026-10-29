/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.GenericWire
public import Rhone.Computation.GenericLinear
public import Mathlib.Algebra.Order.Field.Rat
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic

/-! # General-allele q certificate request reader -/
@[expose] public section
namespace Rhone.Computation.GenericQWire
open Lean
structure Request where
  params : Params
  config : Rhone.Computation.Config
  claimed : Rat
  rawRows : Array (Rhone.Computation.Config × Rat)

def Request.target (r : Request) := GenericWire.toSpec r.params.piA.size r.params.piB.size r.config

def Request.table (r : Request) : GenericWire.Request :=
  ⟨r.params, max r.target.nA r.target.nB, r.rawRows⟩

def Request.accepted (r : Request) : Bool :=
  (r.config.a.size == r.params.piA.size && r.config.b.size == r.params.piB.size &&
    r.config.c.size == r.params.piA.size * r.params.piB.size) &&
    (r.table.accepted && decide (GenericRows.value r.table.rows r.target = r.claimed))

def decode (doc : Json) : Except String Request := do
  GenericWire.fieldsAllowed doc ["op", "key", "q", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
    "entries", "rhone_version", "provenance"]
  let operation ← doc.getObjValAs? String "op"
  let key ← doc.getObjValAs? String "key"
  if operation != "q" then throw "unsupported operation"
  let p ← ParamsWire.decode doc
  if !GenericWire.valid p then throw "invalid general-q parameters"
  let config ← parseConfig key p.piA.size p.piB.size
  let claimed ← doc.getObjValAs? String "q" >>= RationalWire.decode
  let entries ← (doc.getObjVal? "entries" >>= Json.getArr?)
  let rows ← entries.mapM (GenericWire.entry p.piA.size p.piB.size)
  return ⟨p, config, claimed, rows⟩

def checkRequest (doc : Json) : Except String Bool := do
  let r ← decode doc
  return r.accepted

def request (line : String) : Except String Bool := Json.parse line >>= checkRequest

lemma Request.accepted_spec {r : Request} (h : r.accepted = true) :
    ∃ (hA : 0 < r.params.thetaA) (hB : 0 < r.params.thetaB) (hR : 0 ≤ r.params.rho),
      r.claimed = Rhone.LinearAlgebra.Recursion.q
        (πA := GenericWire.pi r.params.piA) (πB := GenericWire.pi r.params.piB)
        hA hB hR r.target := by
  simp only [Request.accepted, Bool.and_eq_true, decide_eq_true_eq] at h
  have hg := h.2.1
  simp only [GenericWire.Request.accepted, Bool.and_eq_true] at hg
  obtain ⟨hA, hB, hR, hq⟩ := GenericRows.check_sound hg.2
  refine ⟨hA, hB, hR, ?_⟩
  rw [← h.2.2]
  exact hq.1 r.target ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

lemma Request.accepted_reference {r : Request} (h : r.accepted = true) :
    r.claimed = GenericLinear.qValue r.params.thetaA r.params.thetaB r.params.rho
      (GenericWire.pi r.params.piA) (GenericWire.pi r.params.piB) r.target := by
  obtain ⟨hA, hB, hR, hq⟩ := Request.accepted_spec h
  rw [GenericLinear.qValue_eq_q hA hB hR, hq]


@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl
@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl
@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl
@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl
private theorem of_bind_ok {α β : Type} {x : Except String α}
    {f : α → Except String β} {b : β} {P : Prop}
    (h : (x >>= f) = .ok b) (k : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases hx : x with
  | error e => simp [hx] at h
  | ok a => exact k a hx (by simpa [hx] using h)

lemma checkRequest_ok (doc : Json) (b : Bool) (h : checkRequest doc = .ok b) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = b := by
  unfold checkRequest at h
  refine of_bind_ok h fun r hr h => ?_
  exact ⟨r, hr, Except.ok.inj h⟩

lemma decode_supplied_fields (doc : Json) (r : Request) (h : decode doc = .ok r) :
    doc.getObjValAs? String "op" = .ok "q" ∧
    ParamsWire.decode doc = .ok r.params ∧ GenericWire.valid r.params = true ∧
    ∃ key, doc.getObjValAs? String "key" = .ok key ∧
      parseConfig key r.params.piA.size r.params.piB.size = .ok r.config ∧
      r.config.key = key ∧
      (doc.getObjValAs? String "q" >>= RationalWire.decode) = .ok r.claimed ∧
      ∃ js : Array Json, (doc.getObjVal? "entries" >>= Json.getArr?) = .ok js ∧
        js.mapM (GenericWire.entry r.params.piA.size r.params.piB.size) = .ok r.rawRows := by
  unfold decode at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun op hop h => ?_
  refine of_bind_ok h fun key hkey h => ?_
  by_cases ho : op = "q"
  · simp only [ho, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine of_bind_ok h fun p hp h => ?_
    cases hv : GenericWire.valid p with
    | false => simp [hv] at h
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      refine of_bind_ok h fun config hc h => ?_
      refine of_bind_ok h fun claimed hvalue h => ?_
      refine of_bind_ok h fun js hjs h => ?_
      refine of_bind_ok h fun rows hm h => ?_
      obtain rfl := Except.ok.inj h
      exact ⟨ho ▸ hop, hp, hv, key, hkey, hc, key_eq_of_parseConfig_eq_ok hc, hvalue, js, hjs, hm⟩
  · simp [ho] at h

lemma checkRequest_accepts_original_value (doc : Json) (h : checkRequest doc = .ok true) :
    ∃ r : Request, decode doc = .ok r ∧
      r.claimed = GenericLinear.qValue r.params.thetaA r.params.thetaB r.params.rho
        (GenericWire.pi r.params.piA) (GenericWire.pi r.params.piB) r.target := by
  obtain ⟨r, hr, ha⟩ := checkRequest_ok _ _ h
  exact ⟨r, hr, Request.accepted_reference ha⟩

lemma request_accepts_original_value (line : String) (h : request line = .ok true) :
    ∃ doc : Json, Json.parse line = .ok doc ∧
      ∃ r : Request, decode doc = .ok r ∧
        r.claimed = GenericLinear.qValue r.params.thetaA r.params.thetaB r.params.rho
          (GenericWire.pi r.params.piA) (GenericWire.pi r.params.piB) r.target := by
  unfold request at h
  refine of_bind_ok h fun doc hp hc => ?_
  exact ⟨doc, hp, checkRequest_accepts_original_value doc hc⟩


lemma Request.accepted_probability {r : Request} (h : r.accepted = true) :
    (r.claimed : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
      (r.params.thetaA : Real) (r.params.thetaB : Real) (r.params.rho : Real)
      (fun i => (GenericWire.pi r.params.piA i : Real))
      (fun j => (GenericWire.pi r.params.piB j : Real)) r.target := by
  have hh := h
  simp only [Request.accepted, Bool.and_eq_true] at hh
  have hv := hh.2.1
  simp only [GenericWire.Request.accepted, Bool.and_eq_true, GenericWire.valid,
    decide_eq_true_eq] at hv
  obtain ⟨⟨⟨_, _, _, _, _, _, _, hpa, hpb, hsa, hsb⟩, _⟩, _⟩ := hv
  obtain ⟨hA, hB, hR, hq⟩ := Request.accepted_spec h
  rw [hq]
  exact QProbability.rat_q_probability _ _ _ _ _ hA hB hR
    (fun i => (hpa i).le) hsa (fun j => (hpb j).le) hsb _

lemma Request.accepted_shapes {r : Request} (h : r.accepted = true) :
    r.config.a.size = r.params.piA.size ∧ r.config.b.size = r.params.piB.size ∧
      r.config.c.size = r.params.piA.size * r.params.piB.size := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩


def requestFields (r : Request) : List (String × Json) :=
  [("op", .str "q"), ("key", .str r.config.key),
    ("q", .str (RationalWire.strictPrint r.claimed))] ++ ParamsWire.fields r.params ++
    [("entries", .arr (r.rawRows.map GenericWire.encodeEntry))]
def encode (r : Request) : Json := Json.mkObj (requestFields r)

private theorem fieldsAllowed_mkObj (fields : List (String × Json)) (allowed : List String)
    (h : ∀ p ∈ fields, p.1 ∈ allowed) :
    GenericWire.fieldsAllowed (Json.mkObj fields) allowed = .ok () := by
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
  unfold GenericWire.fieldsAllowed
  change (if (Std.TreeMap.Raw.ofList fields compare).toList.all
    (fun p => allowed.contains p.1) then Except.ok ()
    else Except.error "unsupported general-table field") = Except.ok ()
  rw [ha]
  rfl

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value := by
  have hd : (requestFields r).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [requestFields, ParamsWire.fields]
  have hl := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hd hmem
  change (Std.TreeMap.Raw.ofList (requestFields r) compare).get? name = some value at hl
  change (match (Std.TreeMap.Raw.ofList (requestFields r) compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hl]

private theorem encode_parameter_getters (r : Request) {name : String} {value : Json}
    (hmem : (name, value) ∈ ParamsWire.fields r.params) :
    (encode r).getObjVal? name = (ParamsWire.encode r.params).getObjVal? name := by
  rw [encode_getObjVal (value := value) (by simp [requestFields, hmem]),
    ParamsWire.encode_getObjVal hmem]

theorem decode_parameters_encode (r : Request) : ParamsWire.decode (encode r) = .ok r.params := by
  have hθA := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("theta_a", Json.str (RationalWire.strictPrint r.params.thetaA)) ∈ ParamsWire.fields r.params)
  have hθB := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("theta_b", Json.str (RationalWire.strictPrint r.params.thetaB)) ∈ ParamsWire.fields r.params)
  have hρ := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("rho", Json.str (RationalWire.strictPrint r.params.rho)) ∈ ParamsWire.fields r.params)
  have hπA := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("pi_a", Json.arr (r.params.piA.map fun q => Json.str (RationalWire.strictPrint q))) ∈
        ParamsWire.fields r.params)
  have hπB := encode_parameter_getters r
    (by simp [ParamsWire.fields] :
      ("pi_b", Json.arr (r.params.piB.map fun q => Json.str (RationalWire.strictPrint q))) ∈
        ParamsWire.fields r.params)
  rw [ParamsWire.decode_congr hθA hθB hρ hπA hπB, ParamsWire.decode_encode]

private lemma encode_str_getter (r : Request) (name value : String)
    (hmem : (name, Json.str value) ∈ requestFields r) :
    (encode r).getObjValAs? String name = .ok value := by
  change Json.getStr? (((encode r).getObjVal? name).toOption.getD .null) = _
  rw [encode_getObjVal hmem]
  rfl

private lemma encode_rows_getter (r : Request) :
    ((encode r).getObjVal? "entries" >>= Json.getArr?) =
      .ok (r.rawRows.map GenericWire.encodeEntry) := by
  have hf := encode_getObjVal (r := r)
    (by simp [requestFields] :
      ("entries", Json.arr (r.rawRows.map GenericWire.encodeEntry)) ∈ requestFields r)
  rw [hf]
  rfl

private lemma encode_fields_allowed (r : Request) :
    GenericWire.fieldsAllowed (encode r)
      ["op", "key", "q", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
        "entries", "rhone_version", "provenance"] = .ok () := by
  apply fieldsAllowed_mkObj
  simp [requestFields, ParamsWire.fields]

lemma decode_encode (r : Request) (hv : GenericWire.valid r.params = true)
    (hc : GenericWire.BoundedConfig r.params.piA.size r.params.piB.size r.config)
    (hrows : ∀ row ∈ r.rawRows,
      GenericWire.BoundedConfig r.params.piA.size r.params.piB.size row.1) :
    decode (encode r) = .ok r := by
  have hvalid := hv
  simp only [GenericWire.valid, decide_eq_true_eq] at hvalid
  obtain ⟨_, _, _, hka, hka255, hkb, hkb255, _, _, _, _⟩ := hvalid
  have hentries := GenericWire.entries_encode _ _ r.rawRows hka hkb hka255 hkb255 hrows
  rw [Array.mapM_map] at hentries
  obtain ⟨ha, hb, hshape, hcounts⟩ := hc
  have hconfig := parseConfig_key r.config _ _ hka hkb hka255 hkb255 ha hb hshape hcounts
  have ho := encode_str_getter r "op" "q" (by simp [requestFields])
  have hk := encode_str_getter r "key" r.config.key (by simp [requestFields])
  have hvalue := encode_str_getter r "q" (RationalWire.strictPrint r.claimed)
    (by simp [requestFields])
  simp [decode, encode_fields_allowed, ho, hk, decode_parameters_encode, hv, hconfig, hvalue,
    RationalWire.decode_strictPrint, encode_rows_getter, hentries]

lemma decode_fields_allowed (doc : Json) (r : Request) (h : decode doc = .ok r) :
    GenericWire.fieldsAllowed doc
      ["op", "key", "q", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
        "entries", "rhone_version", "provenance"] = .ok () := by
  unfold decode at h
  refine of_bind_ok h fun x hx _ => ?_
  cases x
  exact hx

lemma Request.accepted_preserves_config {r : Request} (h : r.accepted = true) :
    GenericWire.fromSpec r.target = r.config := by
  obtain ⟨ha, hb, hc⟩ := Request.accepted_shapes h
  exact GenericWire.fromSpec_toSpec _ _ r.config ha hb hc


def result (value : Rat) : Json := Json.mkObj [("q", .str (RationalWire.strictPrint value))]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  if r.accepted then return result r.claimed
  else throw "incomplete or incorrect general-q certificate"

def response (line : String) : Except String Json := Json.parse line >>= requestAst

lemma requestAst_ok (doc value : Json) (h : requestAst doc = .ok value) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = true ∧ value = result r.claimed := by
  unfold requestAst at h
  refine of_bind_ok h fun r hr h => ?_
  cases ha : r.accepted with
  | false => simp [ha] at h
  | true =>
    simp only [ha, ↓reduceIte, pure_def] at h
    exact ⟨r, hr, ha, (Except.ok.inj h).symm⟩

lemma requestAst_correct (doc value : Json) (h : requestAst doc = .ok value) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = true ∧
      value = result (GenericLinear.qValue r.params.thetaA r.params.thetaB r.params.rho
        (GenericWire.pi r.params.piA) (GenericWire.pi r.params.piB) r.target) := by
  obtain ⟨r, hr, ha, he⟩ := requestAst_ok doc value h
  exact ⟨r, hr, ha, he.trans (congrArg result (Request.accepted_reference ha))⟩

lemma requestAst_refuses {doc : Json} {r : Request} (hd : decode doc = .ok r)
    (h : r.accepted = false) :
    requestAst doc = .error "incomplete or incorrect general-q certificate" := by
  simp [requestAst, hd, h]

end Rhone.Computation.GenericQWire
