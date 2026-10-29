/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericArtifact
public import Rhone.Computation.GenericKernelProof
public import Rhone.Computation.TableArtifactProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
public import Std.Data.TreeMap.Raw.Lemmas

/-! # Meaning of acceptance of the general-allele table artifact reader -/

@[expose] public section
namespace Rhone.Computation.GenericArtifact
open Lean TableArtifact

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => cases h
  | ok a => exact step a rfl h

private theorem require_ok {b : Bool} {m : String} {u : Unit} (h : require b m = .ok u) :
    b = true := by
  cases b
  · cases h
  · rfl

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

theorem valuesMatch_spec {h : Header} {values : Array Rat} {certificate : Array (Config × Rat)}
    (hm : valuesMatch h values certificate = true) :
    ∀ c, c < h.configs.size → ∃ e ∈ certificate.toList,
      e.1 = h.configs.getD c default ∧ e.2 = values.getD c 0 := by
  unfold valuesMatch at hm
  split at hm
  · cases hm
  rename_i t ht
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hm
  intro c hc
  have hget := hm c hc
  rw [GenericKernel.insertRows_get _ _ _ ht] at hget
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty, Option.or_none,
    Option.map_eq_some_iff] at hget
  obtain ⟨e, hfind, hv⟩ := hget
  refine ⟨e, List.mem_of_find?_eq_some hfind, ?_, hv⟩
  have hk := List.find?_some hfind
  simp only [beq_iff_eq] at hk
  exact GenericKernel.keyOf_inj hk

theorem Request.accepted_probability {r : Request} (ha : r.accepted = true)
    {g c : Nat} (hg : g < r.header.grid.size) (hc : c < r.header.configs.size) :
    ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
      (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
      (fun i => (GenericWire.pi r.header.piA i : Real))
      (fun j => (GenericWire.pi r.header.piB j : Real))
      (GenericWire.toSpec r.header.piA.size r.header.piB.size
        (r.header.configs.getD c default)) := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at ha
  obtain ⟨_, hall⟩ := ha
  have hrow := hall g hg
  simp only [rowAccepted, Bool.and_eq_true] at hrow
  obtain ⟨⟨_, hcheck⟩, hmatch⟩ := hrow
  obtain ⟨e, he, hconf, hval⟩ := valuesMatch_spec hmatch c hc
  rw [GenericKernel.Request.accepted_eq] at hcheck
  have hp := GenericWire.Request.accepted_probability _ hcheck e he
  rw [← hval, ← hconf]
  exact hp

theorem decodeHeaderAs_configs {schema : String} {allowed : List String} {doc : Json}
    {h : Header} (hd : decodeHeaderAs schema allowed doc = .ok h) :
    List.Forall₂ (fun key config => parseConfig key h.piA.size h.piB.size = .ok config)
      h.keys.toList h.configs.toList := by
  unfold decodeHeaderAs at hd
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ hka hd => ?_
  refine of_bind_ok hd fun _ hkb hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ hcfg hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  cases hd
  have hka' := require_ok hka
  have hkb' := require_ok hkb
  simp only [beq_iff_eq] at hka' hkb'
  dsimp only
  rw [hka', hkb']
  exact array_mapM_forall2 _ _ _ hcfg

theorem decode_header {doc : Json} {r : Request} (hd : decode doc = .ok r) :
    ∃ table : Json, decodeHeader table = .ok r.header := by
  unfold decode at hd
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  split at hd
  · cases hd
  refine of_bind_ok hd fun table _ hd => ?_
  refine of_bind_ok hd fun header hh hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  cases hd
  exact ⟨table, hh⟩

theorem header_accepted_probability {schema : String} {allowed : List String} {table : Json}
    {r : Request} (hh : decodeHeaderAs schema allowed table = .ok r.header)
    (ha : r.accepted = true) {g c : Nat}
    (hg : g < r.header.grid.size) (hc : c < r.header.keys.size) :
    ∃ config : Config,
      parseConfig (r.header.keys.getD c "") r.header.piA.size r.header.piB.size = .ok config ∧
      ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
        (fun i => (GenericWire.pi r.header.piA i : Real))
        (fun j => (GenericWire.pi r.header.piB j : Real))
        (GenericWire.toSpec r.header.piA.size r.header.piB.size config) := by
  obtain ⟨hlen, hall⟩ := List.forall₂_iff_get.mp (decodeHeaderAs_configs hh)
  simp only [Array.length_toList] at hlen
  have hc' : c < r.header.configs.size := hlen ▸ hc
  refine ⟨r.header.configs.getD c default, ?_, Request.accepted_probability ha hg hc'⟩
  have := hall c (by simpa using hc) (by simpa using hc')
  simpa [Array.getD, hc, hc'] using this

theorem decode_accepted_probability {doc : Json} {r : Request} (hd : decode doc = .ok r)
    (ha : r.accepted = true) {g c : Nat} (hg : g < r.header.grid.size)
    (hc : c < r.header.keys.size) :
    ∃ config : Config,
      parseConfig (r.header.keys.getD c "") r.header.piA.size r.header.piB.size = .ok config ∧
      ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
        (fun i => (GenericWire.pi r.header.piA i : Real))
        (fun j => (GenericWire.pi r.header.piB j : Real))
        (GenericWire.toSpec r.header.piA.size r.header.piB.size config) := by
  obtain ⟨_, hh⟩ := decode_header hd
  exact header_accepted_probability (schema := "rhone-table-v3") (allowed := tableFields) hh ha
    hg hc

theorem requestAst_accept_probability (doc out : Json) (hok : requestAst doc = .ok out)
    (haccept : out.getObjVal? "accepted" = .ok (toJson true)) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = true ∧
      ∀ g c, g < r.header.grid.size → c < r.header.keys.size →
        ∃ config : Config,
          parseConfig (r.header.keys.getD c "") r.header.piA.size r.header.piB.size =
            .ok config ∧
          ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
            (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
            (fun i => (GenericWire.pi r.header.piA i : Real))
            (fun j => (GenericWire.pi r.header.piB j : Real))
            (GenericWire.toSpec r.header.piA.size r.header.piB.size config) := by
  unfold requestAst at hok
  refine of_bind_ok hok fun r hr hok => ?_
  cases hok
  have hacc : r.accepted = true := by
    have h1 : (stamp r.accepted r).getObjVal? "accepted" = .ok (toJson r.accepted) := by
      apply mkObj_getObjVal
      · simp
      · simp
    rw [h1] at haccept
    have := Except.ok.inj haccept
    cases hb : r.accepted
    · rw [hb] at this; cases this
    · rfl
  exact ⟨r, hr, hacc, fun g c hg hc => decode_accepted_probability hr hacc hg hc⟩

end Rhone.Computation.GenericArtifact
