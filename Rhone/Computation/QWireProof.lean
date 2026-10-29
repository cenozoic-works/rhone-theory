/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.QWire
public import Rhone.Computation.QProbabilityProof
public import Rhone.Computation.CheckerWireEntryProof
public import Rhone.Computation.ParamsWireTypedProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
/-! # The production q reader's supplied-input and probability-law fidelity -/
@[expose] public section
open Lean Rhone.Computation
namespace Rhone.Computation.QWire

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl
@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl
@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl
@[simp] private theorem pure_def {α : Type} (x : α) :
    (pure x : Except String α) = Except.ok x := rfl

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, ∃ v : Rat, decode doc = .ok r ∧ r.evaluate = .ok v ∧ out = result v := by
  unfold requestAst at hok
  cases hr : decode doc with
  | error e => simp [hr] at hok
  | ok r =>
    cases hv : r.evaluate with
    | error e => simp [hr, hv] at hok
    | ok v =>
      simp only [hr, hv, ok_bind, pure_def, Except.ok.injEq] at hok
      exact ⟨r, v, rfl, hv, hok.symm⟩

theorem q_success_domain (p : Params) (c : Config) (v : Rat) (hq : q p c = .ok v) :
    p.valid = true ∧ c.a.size = 2 ∧ c.b.size = 2 ∧ c.c.size = 4 := by
  cases hp : p.valid with
  | false => simp [q, hp] at hq
  | true =>
    by_cases ha : c.a.size = 2
    · by_cases hb : c.b.size = 2
      · by_cases hc : c.c.size = 4
        · exact ⟨rfl, ha, hb, hc⟩
        · simp [q, hp, ha, hb, hc] at hq
      · simp [q, hp, hb] at hq
    · simp [q, hp, ha] at hq

theorem requestAst_probability (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ (r : Request) (v : Rat), decode doc = .ok r ∧ out = result v ∧
      r.params.valid = true ∧ r.config.a.size = 2 ∧ r.config.b.size = 2 ∧ r.config.c.size = 4 ∧
      (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.params.thetaA : Real) (r.params.thetaB : Real) (r.params.rho : Real)
        (fun i : Fin 2 => (r.params.piA.getD i.val 0 : Real))
        (fun j : Fin 2 => (r.params.piB.getD j.val 0 : Real))
        (CheckerEncoding.decode r.config) := by
  obtain ⟨r, v, hr, hv, hout⟩ := requestAst_ok doc out hok
  obtain ⟨hp, ha, hb, hc⟩ := q_success_domain r.params r.config v hv
  obtain ⟨w, hw, hprob⟩ := QProbability.compute_q_probability r.params r.config hp ha hb hc
  have hval : v = w := Except.ok.inj (hv.symm.trans hw)
  subst w
  exact ⟨r, v, hr, hout, hp, ha, hb, hc, hprob⟩
private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => simp at h
  | ok a => exact step a rfl h

theorem decode_supplied_fields (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    (doc.getObjVal? "op").bind Json.getStr? = .ok "q" ∧
      ∃ key : String, (doc.getObjVal? "key").bind Json.getStr? = .ok key ∧
        parseConfig key = .ok r.config ∧ ParamsWire.decode doc = .ok r.params := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun operation hop h => ?_
  refine of_bind_ok h fun key hkey h => ?_
  by_cases hoperation : operation = "q"
  · simp only [hoperation, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine of_bind_ok h fun config hc h => ?_
    refine of_bind_ok h fun params hp h => ?_
    obtain rfl := Except.ok.inj h
    exact ⟨hoperation ▸ hop, key, hkey, hc, hp⟩
  · simp [hoperation] at h

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
  apply (ParamsWire.decodeTyped_eq_ok_iff _ _).mp
  rw [ParamsWire.decodeTyped_congr hθA hθB hρ hπA hπB, ParamsWire.decodeTyped_encode]

theorem decode_encode (r : Request) (hconfig : CheckerWire.BoundedConfig r.config) :
    decode (encode r) = .ok r := by
  have hop := encode_getObjVal (r := r)
    (by simp [requestFields] : ("op", .str "q") ∈ requestFields r)
  have hkey := encode_getObjVal (r := r)
    (by simp [requestFields] : ("key", .str r.config.key) ∈ requestFields r)
  obtain ⟨ha, hb, hc, hu⟩ := hconfig
  have hk := parseConfig_key r.config 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ha hb (by simpa using hc) hu
  simp [decode, hop, hkey, Except.bind, Json.getStr?, hk, decode_parameters_encode]

theorem requestAst_encode (r : Request) (hconfig : CheckerWire.BoundedConfig r.config)
    (value : Rat) (hq : r.evaluate = .ok value) :
    requestAst (encode r) = .ok (result value) := by
  simp [requestAst, decode_encode r hconfig, hq]
theorem request_ok (line : String) (out : Json) (hok : request line = .ok out) :
    ∃ doc : Json, Json.parse line = .ok doc ∧ requestAst doc = .ok out := by
  unfold request at hok
  cases h : Json.parse line with
  | error e => simp [h] at hok
  | ok doc =>
    simp only [h, ok_bind] at hok
    exact ⟨doc, rfl, hok⟩

theorem requestAst_eq_reference (doc : Json) : requestAst doc = (do
    let operation ← (doc.getObjVal? "op").bind Json.getStr?
    let key ← (doc.getObjVal? "key").bind Json.getStr?
    if operation != "q" then throw "unsupported operation"
    let config ← parseConfig key
    let params ← ParamsWire.decode doc
    let value ← q params config
    return result value) := by
  simp only [requestAst, decode]
  cases ho : (doc.getObjVal? "op").bind Json.getStr? with
  | error e => simp [Except.bind]
  | ok operation =>
    cases hk : (doc.getObjVal? "key").bind Json.getStr? with
    | error e => simp
    | ok key =>
      by_cases hop : operation = "q"
      · cases hc : parseConfig key <;> cases hp : ParamsWire.decode doc <;>
          simp_all [Request.evaluate, Except.bind]
      · simp [hop]
end Rhone.Computation.QWire
