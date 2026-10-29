/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftFull
public import Rhone.Computation.DriftLawProof
public import Rhone.Computation.DriftWireProof
public import Rhone.Computation.AbsorptionProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas

/-!
# The drift reader that compares the distribution, the heterozygosity, and the absorption time
-/

@[expose] public section
namespace Rhone.Computation.DriftFull
open Lean MarkovChain MeasureTheory

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

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

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => simp at h
  | ok a => exact step a rfl h

theorem Request.check_iff (r : Request) :
    r.check = true ↔ r.base.check = true ∧ r.distribution = r.law ∧
      r.heterozygosity = Drift.lawHeterozygosity r.base.geneCopies r.law ∧
      r.tableCheck = true ∧ r.absorption = r.table.getD r.base.initialCount 0 := by
  unfold Request.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

private theorem stamp_fields (d : Bool × Nat) :
    ([("schema", toJson "rhone-compute-drift-full-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
  simp

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have ha : ∀ d : Bool × Nat, (stamp d).getObjVal? "accepted" = .ok (.bool d.1) :=
    fun d => mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hc : ∀ d : Bool × Nat,
      (stamp d).getObjValAs? Nat "checked_rational_values" = .ok d.2 :=
    fun d => getNat_of (mkObj_getObjVal (stamp_fields d) (by simp))
  have h1 := ha first
  have h2 := hc first
  rw [h] at h1 h2
  rw [ha second] at h1
  rw [hc second] at h2
  cases first
  cases second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2
  simp [h1, h2]

theorem stamp_ne_wire_stamp (d : Bool × Nat) (e : Bool × Nat × Bool) :
    stamp d ≠ DriftWire.stamp e := by
  intro h
  have h1 : (stamp d).getObjVal? "schema" =
      .ok (.str "rhone-compute-drift-full-check-v1") :=
    mkObj_getObjVal (stamp_fields d) (by simp [toJson])
  have hfields : ([("schema", toJson "rhone-compute-drift-check-v1"),
      ("accepted", toJson e.1), ("checked_rational_values", toJson e.2.1),
      ("neutral_heterozygosity_checked", toJson e.2.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
      List (String × Json)).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp
  have h2 : (DriftWire.stamp e).getObjVal? "schema" =
      .ok (.str "rhone-compute-drift-check-v1") :=
    mkObj_getObjVal hfields (by simp [toJson])
  rw [h, h2] at h1
  simp at h1

theorem decode_base (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    DriftWire.decode doc = .ok r.base := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun base hbase h => ?_
  refine of_bind_ok h fun distribution _ h => ?_
  refine of_bind_ok h fun heterozygosity _ h => ?_
  refine of_bind_ok h fun absorption _ h => ?_
  refine of_bind_ok h fun table _ h => ?_
  obtain rfl := Except.ok.inj h
  exact hbase

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.base.valid = true ∧
      out = stamp (r.check, r.count) := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.base.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      refine ⟨r, rfl, hvalid, ?_⟩
      simpa [hdecode, hvalid, Except.map] using hok.symm

theorem decision_wire (doc : Json) (d : Bool × Nat) (h : decision doc = .ok d) :
    ∃ e : Bool × Nat × Bool, DriftWire.decision doc = .ok e ∧ (d.1 = true → e.1 = true) := by
  unfold decision at h
  cases hdecode : decode doc with
  | error message => simp [hdecode] at h
  | ok r =>
    cases hvalid : r.base.valid with
    | false => simp [hdecode, hvalid] at h
    | true =>
      have hd : d = (r.check, r.count) := by simpa [hdecode, hvalid] using h.symm
      refine ⟨(r.base.check, r.base.claim.size, r.base.neutral), ?_, ?_⟩
      · simp [DriftWire.decision, decode_base doc r hdecode, hvalid]
      · intro hcheck
        rw [hd] at hcheck
        exact ((Request.check_iff r).mp hcheck).1

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.base.valid = true ∧ r.base.check = true ∧
      r.distribution = r.law ∧
      r.heterozygosity = Drift.lawHeterozygosity r.base.geneCopies r.law ∧
      r.tableCheck = true ∧ r.absorption = r.table.getD r.base.initialCount 0 ∧
      count = r.count := by
  obtain ⟨r, hdecode, hvalid, hout⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hbase, hlaw, hhet, htable, habs⟩ := (Request.check_iff r).mp hpair.1.symm
  exact ⟨r, hdecode, hvalid, hbase, hlaw, hhet, htable, habs, hpair.2⟩

theorem requestAst_accept_wire (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ (size : Nat) (neutral : Bool),
      DriftWire.requestAst doc = .ok (DriftWire.stamp (true, size, neutral)) := by
  obtain ⟨r, hdecode, hvalid, hbase, -⟩ := requestAst_accept_sound doc count haccept
  refine ⟨r.base.claim.size, r.base.neutral, ?_⟩
  simp [DriftWire.requestAst, DriftWire.decision, decode_base doc r hdecode, hvalid, hbase,
    Except.map]

theorem requestAst_accept_law (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 < r.base.geneCopies ∧
      r.distribution.size = r.base.geneCopies + 1 ∧
      ∀ x : Fin (r.base.geneCopies + 1), (x : Nat) = r.base.initialCount →
        (r.base.moran = false →
          (∀ j : Fin (r.base.geneCopies + 1), (r.distribution.getD j 0 : Real) =
            ((wfChain r.base.geneCopies).pathLaw x).real {ω | ω r.base.steps = j}) ∧
          (r.heterozygosity : Real) =
            ∫ ω, Rhone.MarkovChain.het r.base.geneCopies (ω r.base.steps)
              ∂(wfChain r.base.geneCopies).pathLaw x ∧
          ∫⁻ ω, (hitTime (fixationBoundary r.base.geneCopies) ω : ENNReal)
            ∂(wfChain r.base.geneCopies).pathLaw x =
              ENNReal.ofReal (r.absorption : Real)) ∧
        (r.base.moran = true → ∃ hr : 0 < (r.base.fitness : Real),
          (∀ j : Fin (r.base.geneCopies + 1), (r.distribution.getD j 0 : Real) =
            ((moranChain r.base.geneCopies (r.base.fitness : Real) hr).pathLaw x).real
              {ω | ω r.base.steps = j}) ∧
          (r.heterozygosity : Real) =
            ∫ ω, Rhone.MarkovChain.het r.base.geneCopies (ω r.base.steps)
              ∂(moranChain r.base.geneCopies (r.base.fitness : Real) hr).pathLaw x ∧
          ∫⁻ ω, (hitTime (fixationBoundary r.base.geneCopies) ω : ENNReal)
            ∂(moranChain r.base.geneCopies (r.base.fitness : Real) hr).pathLaw x =
              ENNReal.ofReal (r.absorption : Real)) := by
  obtain ⟨r, hdecode, hvalid, -, hlaw, hhet, htable, habs, -⟩ :=
    requestAst_accept_sound doc count haccept
  obtain ⟨hn, -, -, -, hfitness⟩ := (DriftWire.Request.valid_iff r.base).mp hvalid
  have hsize : r.distribution.size = r.base.geneCopies + 1 := by
    rw [hlaw]
    unfold Request.law
    split
    · exact Drift.moranDistribution_size _ _ _ _
    · exact Drift.wfDistribution_size _ _ _
  refine ⟨r, hdecode, hn, hsize, fun x hx => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · have hwf : r.law = Drift.wfDistribution r.base.geneCopies x r.base.steps := by
      simp [Request.law, hm, hx]
    have ht : Absorption.checkWf r.base.geneCopies r.table = true := by
      simpa [Request.tableCheck, hm] using htable
    rw [hwf] at hlaw hhet
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rw [hlaw]
      exact Drift.wfDistribution_real _ _ x j
    · rw [hhet]
      exact Drift.wfLawHeterozygosity_integral _ _ x
    · rw [habs, ← hx]
      exact Absorption.checkWf_lintegral_hitTime _ hn r.table ht x
  · have hr : 0 < (r.base.fitness : Real) := Rat.cast_pos.mpr (hfitness hm)
    have hmoran : r.law =
        Drift.moranDistribution r.base.geneCopies r.base.fitness x r.base.steps := by
      simp [Request.law, hm, hx]
    have ht : Absorption.checkMoran r.base.geneCopies r.base.fitness r.table = true := by
      simpa [Request.tableCheck, hm] using htable
    rw [hmoran] at hlaw hhet
    refine ⟨hr, fun j => ?_, ?_, ?_⟩
    · rw [hlaw]
      exact Drift.moranDistribution_real _ _ hr _ x j
    · rw [hhet]
      exact Drift.moranLawHeterozygosity_integral _ _ hr _ x
    · rw [habs, ← hx]
      exact Absorption.checkMoran_lintegral_hitTime _ hn _ hr r.table ht x

end Rhone.Computation.DriftFull
