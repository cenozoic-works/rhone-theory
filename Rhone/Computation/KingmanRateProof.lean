/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.KingmanRate
public import Rhone.Computation.KingmanWireProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
public import Std.Data.TreeMap.Raw.Lemmas

/-! # Fidelity of the Kingman genealogy-moments report reader at a supplied pair rate -/

@[expose] public section
namespace Rhone.Computation.KingmanRate
open Lean KingmanWire

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

theorem valid_iff (r : Request) :
    valid r = true ↔ 1 ≤ r.geneCopies ∧ r.geneCopies ≤ 4096 ∧ 0 < r.pairRate := by
  unfold valid
  rw [decide_eq_true_iff]

theorem reportValues_eq (n : Nat) (c : Rat) :
    reportValues n c =
      #[(Kingman.moments n).meanTmrca / c, (Kingman.moments n).varianceTmrca / c ^ 2,
        (Kingman.moments n).meanTotalBranchLength / c,
        (Kingman.moments n).varianceTotalBranchLength / c ^ 2] := rfl

theorem reportValues_one (n : Nat) : reportValues n 1 = Kingman.reportValues n := by
  simp [reportValues, scaledMoments, Kingman.reportValues]

theorem checkReport_one (n : Nat) (claim : Array Rat) :
    checkReport n 1 claim = Kingman.checkReport n claim := by
  simp [checkReport, Kingman.checkReport, reportValues_one]

theorem checkReport_iff (n : Nat) (c : Rat) (claim : Array Rat) :
    checkReport n c claim = true ↔ claim = reportValues n c := by
  unfold checkReport
  rw [decide_eq_true_iff]

theorem claim_ofFormula (n : Nat) (c : Rat) (unit : String) :
    (ofFormula n c unit).claim = reportValues n c := rfl

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-kingman-rate-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false),
      ("supplied_rate_scaling_proved", toJson true)] :
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

theorem stamp_ne_wire_stamp (d e : Bool × Nat) : stamp d ≠ KingmanWire.stamp e := by
  intro h
  have h1 : (stamp d).getObjVal? "schema" =
      .ok (toJson "rhone-compute-kingman-rate-check-v1") :=
    mkObj_getObjVal (by simp) (by simp)
  have h2 : (KingmanWire.stamp e).getObjVal? "schema" =
      .ok (toJson "rhone-compute-kingman-check-v1") :=
    mkObj_getObjVal (by simp) (by simp)
  rw [h, h2] at h1
  have := Except.ok.inj h1
  simp [toJson] at this

private theorem decision_encode (r : Request) (hcanonical : r.Canonical) :
    decision (encode r) = if valid r then .ok (checkReport r.geneCopies r.pairRate r.claim,
      r.claim.size) else .error "unsupported sample size or pair rate" := by
  simp [decision, decode_encode r hcanonical]

theorem requestAst_encode (r : Request) (hcanonical : r.Canonical) (hvalid : valid r = true) :
    requestAst (encode r) =
      .ok (stamp (checkReport r.geneCopies r.pairRate r.claim, r.claim.size)) := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hcanonical : r.Canonical)
    (hvalid : valid r = false) :
    requestAst (encode r) = .error "unsupported sample size or pair rate" := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ valid r = true ∧
      out = stamp (checkReport r.geneCopies r.pairRate r.claim, r.claim.size) ∧
      requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    have hcanonical := decode_canonical doc r hdecode
    cases hvalid : valid r with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (checkReport r.geneCopies r.pairRate r.claim, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hcanonical, hvalid, hout, hout ▸ requestAst_encode r hcanonical hvalid⟩

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ valid r = true ∧
      r.claim = reportValues r.geneCopies r.pairRate ∧ count = r.claim.size ∧
      requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hcanonical, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  exact ⟨r, hdecode, hcanonical, hvalid, (checkReport_iff _ _ _).mp hpair.1.symm,
    hpair.2, hencode⟩

theorem requestAst_ofFormula (n : Nat) (c : Rat) (unit : String) (hunit : unitOk unit = true)
    (hlower : 1 ≤ n) (hupper : n ≤ 4096) (hc : 0 < c) :
    requestAst (encode (ofFormula n c unit)) =
      .ok (stamp (true, (reportValues n c).size)) := by
  have hcanonical : (ofFormula n c unit).Canonical := hunit
  have hvalid : valid (ofFormula n c unit) = true :=
    (valid_iff _).mpr ⟨hlower, hupper, hc⟩
  rw [requestAst_encode _ hcanonical hvalid]
  have hclaim : (ofFormula n c unit).claim = reportValues n c := rfl
  have : checkReport n c (reportValues n c) = true := (checkReport_iff _ _ _).mpr rfl
  change Except.ok (stamp (checkReport n c (ofFormula n c unit).claim,
    (ofFormula n c unit).claim.size)) = _
  rw [hclaim, this]

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

theorem decision_eq_wire (doc : Json) (hrate : ∀ r, decode doc = .ok r → r.pairRate = 1) :
    decision doc = KingmanWire.decision doc := by
  unfold decision KingmanWire.decision
  cases hdecode : decode doc with
  | error message => rfl
  | ok r =>
    have h1 := hrate r hdecode
    have hv : valid r = r.valid := by
      simp [valid, Request.valid, h1]
    simp [hv, h1, checkReport_one]

theorem decision_of_wire (doc : Json) (d : Bool × Nat)
    (h : KingmanWire.decision doc = .ok d) : decision doc = .ok d := by
  have hrate : ∀ r, decode doc = .ok r → r.pairRate = 1 := by
    intro r hdecode
    unfold KingmanWire.decision at h
    rw [hdecode] at h
    simp only at h
    split at h
    · rename_i hv
      exact ((Request.valid_iff r).mp hv).2.2
    · simp at h
  rw [decision_eq_wire doc hrate]
  exact h

theorem requestAst_accept_law (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ valid r = true ∧ 0 < r.pairRate ∧
      (∫⁻ p, Rhone.Coalescent.tmrca r.geneCopies p
          ∂(Rhone.Coalescent.blockChain r.geneCopies).jumpHoldLaw
            (Fin.last r.geneCopies)) =
        ENNReal.ofReal ((r.pairRate * r.meanTmrca : Rat) : Real) ∧
      ProbabilityTheory.variance (fun p => (Rhone.Coalescent.tmrca r.geneCopies p).toReal)
          ((Rhone.Coalescent.blockChain r.geneCopies).jumpHoldLaw (Fin.last r.geneCopies)) =
        ((r.pairRate ^ 2 * r.varianceTmrca : Rat) : Real) ∧
      (∫⁻ p, Rhone.Coalescent.treeLength r.geneCopies p
          ∂(Rhone.Coalescent.blockChain r.geneCopies).jumpHoldLaw
            (Fin.last r.geneCopies)) =
        ENNReal.ofReal ((r.pairRate * r.meanTotalBranchLength : Rat) : Real) ∧
      ProbabilityTheory.variance
          (fun p => (Rhone.Coalescent.treeLength r.geneCopies p).toReal)
          ((Rhone.Coalescent.blockChain r.geneCopies).jumpHoldLaw (Fin.last r.geneCopies)) =
        ((r.pairRate ^ 2 * r.varianceTotalBranchLength : Rat) : Real) := by
  obtain ⟨r, hdecode, -, hvalid, hclaim, -, -⟩ := requestAst_accept_sound doc count haccept
  have hc : 0 < r.pairRate := ((valid_iff r).mp hvalid).2.2
  have hne : r.pairRate ≠ 0 := hc.ne'
  have hback : (#[r.pairRate * r.meanTmrca, r.pairRate ^ 2 * r.varianceTmrca,
      r.pairRate * r.meanTotalBranchLength, r.pairRate ^ 2 * r.varianceTotalBranchLength] :
      Array Rat) = Kingman.reportValues r.geneCopies := by
    have h4 : r.claim = #[r.meanTmrca, r.varianceTmrca, r.meanTotalBranchLength,
      r.varianceTotalBranchLength] := rfl
    rw [h4, reportValues_eq] at hclaim
    simp only [Array.mk.injEq, List.cons.injEq, and_true] at hclaim
    obtain ⟨e1, e2, e3, e4⟩ := hclaim
    rw [e1, e2, e3, e4]
    simp only [Kingman.reportValues]
    have f1 : ∀ x : Rat, r.pairRate * (x / r.pairRate) = x := fun x => by field_simp
    have f2 : ∀ x : Rat, r.pairRate ^ 2 * (x / r.pairRate ^ 2) = x := fun x => by
      field_simp
    simp only [f1, f2]
  have hcheck := Kingman.Request.check_sound (⟨r.geneCopies, 1⟩ : Kingman.Request)
    (#[r.pairRate * r.meanTmrca, r.pairRate ^ 2 * r.varianceTmrca,
      r.pairRate * r.meanTotalBranchLength, r.pairRate ^ 2 * r.varianceTotalBranchLength])
    (by
      unfold Kingman.Request.check
      rw [hback]
      exact Kingman.checkReport_complete _)
  obtain ⟨-, -, h1, h2, -, h3, h4⟩ := hcheck
  exact ⟨r, hdecode, hvalid, hc, by simpa using h1, by simpa using h2, by simpa using h3,
    by simpa using h4⟩

end Rhone.Computation.KingmanRate
