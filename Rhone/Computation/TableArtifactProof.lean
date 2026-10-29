/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.TableArtifact
public import Rhone.Computation.QProbabilityProof
public import Rhone.Computation.ConfigProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.HashMap.Lemmas

/-! # Meaning of acceptance of the exact two-allele table artifact reader -/

@[expose] public section
namespace Rhone.Computation.TableArtifact
open Lean

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => cases h
  | ok a => exact step a rfl h

theorem list_mapM_forall2 {α β : Type} (f : α → Except String β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil] at h
    cases h
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    refine of_bind_ok h fun y hy h => ?_
    refine of_bind_ok h fun tail ht h => ?_
    cases h
    exact .cons hy (ih tail ht)

theorem array_mapM_forall2 {α β : Type} (f : α → Except String β) (xs : Array α)
    (ys : Array β) (h : xs.mapM f = .ok ys) :
    List.Forall₂ (fun x y => f x = .ok y) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases ht : xs.toList.mapM f with
  | error e => simp [ht] at h
  | ok tail =>
    have he : tail.toArray = ys := by simpa [ht] using h
    rw [← he, List.toList_toArray]
    exact list_mapM_forall2 f xs.toList tail ht

theorem forall2_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : ∀ y ∈ ys, ∃ x ∈ xs, R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | cons hr _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hxy⟩ := ih y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

theorem entry_parse {row : Json} {e : Config × Rat} (h : CheckerWire.entry row = .ok e) :
    parseConfig e.1.key = .ok e.1 := by
  unfold CheckerWire.entry at h
  refine of_bind_ok h fun key _ h => ?_
  refine of_bind_ok h fun value _ h => ?_
  refine of_bind_ok h fun config hc h => ?_
  cases h
  rw [key_eq_of_parseConfig_eq_ok hc]
  exact hc

theorem entries_parse {doc : Json} {rows : Array (Config × Rat)}
    (h : CheckerWire.entries doc = .ok rows) :
    ∀ e ∈ rows, parseConfig e.1.key = .ok e.1 := by
  unfold CheckerWire.entries at h
  refine of_bind_ok h fun arr _ h => ?_
  intro e he
  obtain ⟨x, _, hx⟩ := forall2_mem_right (array_mapM_forall2 _ _ _ h) e (by simpa using he)
  exact entry_parse hx

theorem lookup_mem {certificate : Array (Config × Rat)} {k : String} {v : Rat}
    (h : (lookup certificate).get? k = some v) :
    ∃ e ∈ certificate, e.1.key = k ∧ e.2 = v := by
  unfold lookup at h
  rw [← Array.foldl_toList] at h
  suffices hs : ∀ (l : List (Config × Rat)) (m : Std.HashMap String Rat),
      (∀ k v, m.get? k = some v → ∃ e ∈ certificate.toList, e.1.key = k ∧ e.2 = v) →
      (∀ e ∈ l, e ∈ certificate.toList) →
      (l.foldl (fun m e => m.insert e.1.key e.2) m).get? k = some v →
      ∃ e ∈ certificate.toList, e.1.key = k ∧ e.2 = v by
    obtain ⟨e, he, hk, hv⟩ := hs certificate.toList {} (fun k v hm => by simp at hm)
      (fun e he => he) h
    exact ⟨e, by simpa using he, hk, hv⟩
  intro l
  induction l with
  | nil => intro m hm _ hl; exact hm k v hl
  | cons e l ih =>
    intro m hm hsub hl
    refine ih (m.insert e.1.key e.2) ?_ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hl
    intro k' v' hk'
    rw [Std.HashMap.get?_insert] at hk'
    split at hk'
    · rename_i heq
      cases hk'
      exact ⟨e, hsub e List.mem_cons_self, by simpa using heq, rfl⟩
    · exact hm k' v' hk'

theorem rowAccepted_spec {h : Header} {rho : Rat} {values : Array Rat}
    {certificate : Array (Config × Rat)} (ha : rowAccepted h rho values certificate = true) :
    values.size = h.keys.size ∧ checkTable (h.params rho) h.n certificate = true ∧
      ∀ c, c < h.keys.size → ∃ e ∈ certificate, e.1.key = h.keys.getD c "" ∧
        e.2 = values.getD c 0 := by
  simp only [rowAccepted, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ha
  obtain ⟨⟨hs, hc⟩, hall⟩ := ha
  exact ⟨hs, hc, fun c hc' => lookup_mem (hall c hc')⟩

theorem Request.accepted_probability {r : Request} (ha : r.accepted = true)
    (hcert : ∀ certificate ∈ r.certificates, ∀ e ∈ certificate, parseConfig e.1.key = .ok e.1)
    {g c : Nat} (hg : g < r.header.grid.size) (hc : c < r.header.keys.size) :
    ∃ config : Config, parseConfig (r.header.keys.getD c "") = .ok config ∧
      ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
        (fun i : Fin 2 => (r.header.piA.getD i.val 0 : Real))
        (fun j : Fin 2 => (r.header.piB.getD j.val 0 : Real))
        (CheckerEncoding.decode config) := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at ha
  obtain ⟨⟨_, hcs⟩, hall⟩ := ha
  obtain ⟨_, hcheck, hcells⟩ := rowAccepted_spec (hall g hg)
  obtain ⟨e, he, hkey, hval⟩ := hcells c hc
  have hmem : r.certificates.getD g #[] ∈ r.certificates := by
    simp [Array.getD, hcs ▸ hg]
  have hparse := hcert _ hmem e he
  rw [hkey] at hparse
  refine ⟨e.1, hparse, ?_⟩
  rw [← hval]
  exact QProbability.checked_table_probability hcheck e he

theorem decode_certificates {doc : Json} {r : Request} (h : decode doc = .ok r) :
    ∀ certificate ∈ r.certificates, ∀ e ∈ certificate, parseConfig e.1.key = .ok e.1 := by
  unfold decode at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun op _ h => ?_
  split at h
  · cases h
  refine of_bind_ok h fun table _ h => ?_
  refine of_bind_ok h fun header _ h => ?_
  refine of_bind_ok h fun values _ h => ?_
  refine of_bind_ok h fun certificates hc h => ?_
  cases h
  refine of_bind_ok hc fun arr _ hc => ?_
  unfold readCertificates at hc
  refine of_bind_ok hc fun arr' _ hc => ?_
  split at hc
  · cases hc
  intro certificate hmem
  obtain ⟨x, _, hx⟩ := forall2_mem_right (array_mapM_forall2 _ _ _ hc) certificate
    (by simpa using hmem)
  exact entries_parse hx

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

theorem stamp_accepted (a : Bool) (r : Request) :
    (stamp a r).getObjVal? "accepted" = .ok (toJson a) := by
  apply mkObj_getObjVal
  · simp
  · simp

theorem requestAst_accept_probability (doc out : Json) (hok : requestAst doc = .ok out)
    (haccept : out.getObjVal? "accepted" = .ok (toJson true)) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = true ∧
      ∀ g c, g < r.header.grid.size → c < r.header.keys.size →
        ∃ config : Config, parseConfig (r.header.keys.getD c "") = .ok config ∧
          ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
            (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
            (fun i : Fin 2 => (r.header.piA.getD i.val 0 : Real))
            (fun j : Fin 2 => (r.header.piB.getD j.val 0 : Real))
            (CheckerEncoding.decode config) := by
  unfold requestAst at hok
  refine of_bind_ok hok fun r hr hok => ?_
  cases hok
  have hacc : r.accepted = true := by
    rw [stamp_accepted] at haccept
    have := Except.ok.inj haccept
    cases hb : r.accepted
    · rw [hb] at this; cases this
    · rfl
  exact ⟨r, hr, hacc, fun g c hg hc =>
    Request.accepted_probability hacc (decode_certificates hr) hg hc⟩

end Rhone.Computation.TableArtifact
