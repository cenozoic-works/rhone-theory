/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.FStatisticsWire
public import Rhone.Computation.FStatisticsProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the F-statistics reader -/

@[expose] public section
namespace Rhone.Computation.FStatisticsWire
open Lean Rhone.Dynamics MarkovChain

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
    (h : object.getObjVal? name = .ok (encodeRat value)) :
    rat object name = .ok value := by
  rw [rat, getStr_of h]
  exact RationalWire.decode_strictPrint value

private theorem encode_getObjVal {r : Request} {name : String} {value : Json}
    (hmem : (name, value) ∈ requestFields r) :
    (encode r).getObjVal? name = .ok value :=
  mkObj_getObjVal (by simp [requestFields]) hmem

private theorem some_getD {o : Option Rat} {q : Rat} (h : o = some q) :
    o = some (o.getD 0) := by
  subst h
  rfl

private theorem some_getD3 {o : Option (Rat × Rat × Rat)} {x : Rat × Rat × Rat}
    (h : o = some x) :
    o = some ((o.getD (0, 0, 0)).1, (o.getD (0, 0, 0)).2.1, (o.getD (0, 0, 0)).2.2) := by
  subst h
  rfl

theorem Request.valid_iff (r : Request) :
    r.valid = true ↔ FStatistics.weightsNormalized r.demes = true ∧
      FStatistics.meanHet r.demes ≠ 0 ∧ FStatistics.pooledHet r.demes ≠ 0 ∧
      r.demes.length ≤ 4096 := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem Request.check_iff (r : Request) :
    r.check = true ↔ r.subpopulation = FStatistics.meanHet r.demes ∧
      r.total = FStatistics.pooledHet r.demes ∧
      FStatistics.fStatistics r.observed (FStatistics.meanHet r.demes)
        (FStatistics.pooledHet r.demes) = some (r.fIS, r.fST, r.fIT) ∧
      FStatistics.wahlundDeficit r.demes = some r.deficit ∧
      FStatistics.wahlundVarianceForm r.demes = some r.varianceForm ∧
      FStatistics.fStWahlund r.demes = some r.fSTWahlund := by
  unfold Request.check
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-f-statistics-check-v1"),
      ("accepted", toJson d.1), ("checked_rational_values", toJson d.2),
      ("json_boundary_equality_proved", toJson false),
      ("rust_implementation_equality_proved", toJson false)] :
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
  obtain ⟨a, c⟩ := first
  obtain ⟨a', c'⟩ := second
  simp only [Except.ok.injEq, Json.bool.injEq] at h1 h2
  simp [h1, h2]

private theorem deme_encodeDeme (d : Rat × Rat) : deme (encodeDeme d) = .ok d := by
  have hw := rat_of (mkObj_getObjVal (fields := demeFields d) (name := "weight")
    (value := encodeRat d.1) (by simp [demeFields]) (by simp [demeFields]))
  have hp := rat_of (mkObj_getObjVal (fields := demeFields d) (name := "frequency")
    (value := encodeRat d.2) (by simp [demeFields]) (by simp [demeFields]))
  simp [deme, encodeDeme, hw, hp]

private theorem list_deme_encode (demes : List (Rat × Rat)) :
    (demes.map encodeDeme).mapM deme = .ok demes := by
  induction demes with
  | nil => rfl
  | cons d demes ih => simp [List.mapM_cons, deme_encodeDeme, ih]

theorem demeArray_encode (demes : List (Rat × Rat)) :
    demeArray (encodeDemes demes) = .ok demes.toArray := by
  have hl := list_deme_encode demes
  unfold demeArray encodeDemes
  change (Except.ok (demes.toArray.map encodeDeme) : Except String (Array Json)) >>= _ = _
  rw [ok_bind, Array.mapM_eq_mapM_toList, Array.toList_map, List.toList_toArray, hl]
  simp

theorem decode_encode (r : Request) : decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-f-statistics-v1") (by simp [requestFields, toJson]))
  have hdemes : ((encode r).getObjVal? "demes").bind demeArray = .ok r.demes.toArray := by
    rw [encode_getObjVal (r := r) (name := "demes") (value := encodeDemes r.demes)
      (by simp [requestFields])]
    exact demeArray_encode r.demes
  have hobserved := rat_of (encode_getObjVal (r := r) (name := "observed_heterozygosity")
    (value := encodeRat r.observed) (by simp [requestFields]))
  have hsub := rat_of (encode_getObjVal (r := r) (name := "subpopulation_heterozygosity")
    (value := encodeRat r.subpopulation) (by simp [requestFields]))
  have htotal := rat_of (encode_getObjVal (r := r) (name := "total_heterozygosity")
    (value := encodeRat r.total) (by simp [requestFields]))
  have h1 := rat_of (encode_getObjVal (r := r) (name := "f_is")
    (value := encodeRat r.fIS) (by simp [requestFields]))
  have h2 := rat_of (encode_getObjVal (r := r) (name := "f_st")
    (value := encodeRat r.fST) (by simp [requestFields]))
  have h3 := rat_of (encode_getObjVal (r := r) (name := "f_it")
    (value := encodeRat r.fIT) (by simp [requestFields]))
  have h4 := rat_of (encode_getObjVal (r := r) (name := "wahlund_deficit")
    (value := encodeRat r.deficit) (by simp [requestFields]))
  have h5 := rat_of (encode_getObjVal (r := r) (name := "wahlund_variance_form")
    (value := encodeRat r.varianceForm) (by simp [requestFields]))
  have h6 := rat_of (encode_getObjVal (r := r) (name := "f_st_wahlund")
    (value := encodeRat r.fSTWahlund) (by simp [requestFields]))
  simp [decode, hschema, hdemes, hobserved, hsub, htotal, h1, h2, h3, h4, h5, h6]

private theorem decision_encode (r : Request) :
    decision (encode r) = if r.valid then .ok (r.check, r.claim.size)
      else .error "unsupported F-statistics request domain" := by
  simp [decision, decode_encode r]

theorem requestAst_encode (r : Request) (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.claim.size)) := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported F-statistics request domain" := by
  simp [requestAst, decision_encode r, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
      out = stamp (r.check, r.claim.size) ∧ requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, r.claim.size) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hvalid, hout, hout ▸ requestAst_encode r hvalid⟩

theorem requestAst_accept_iff (doc : Json) (count : Nat) :
    requestAst doc = .ok (stamp (true, count)) ↔
      ∃ r : Request, decode doc = .ok r ∧ r.valid = true ∧
        r.subpopulation = FStatistics.meanHet r.demes ∧
        r.total = FStatistics.pooledHet r.demes ∧
        FStatistics.fStatistics r.observed (FStatistics.meanHet r.demes)
          (FStatistics.pooledHet r.demes) = some (r.fIS, r.fST, r.fIT) ∧
        FStatistics.wahlundDeficit r.demes = some r.deficit ∧
        FStatistics.wahlundVarianceForm r.demes = some r.varianceForm ∧
        FStatistics.fStWahlund r.demes = some r.fSTWahlund ∧
        count = 8 := by
  constructor
  · intro haccept
    obtain ⟨r, hdecode, hvalid, hout, -⟩ := requestAst_ok doc _ haccept
    have hpair := stamp_injective hout
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (Request.check_iff r).mp hpair.1.symm
    exact ⟨r, hdecode, hvalid, h1, h2, h3, h4, h5, h6, hpair.2⟩
  · rintro ⟨r, hdecode, hvalid, h1, h2, h3, h4, h5, h6, rfl⟩
    have hcheck : r.check = true := (Request.check_iff r).mpr ⟨h1, h2, h3, h4, h5, h6⟩
    simp [requestAst, decision, hdecode, hvalid, hcheck, Except.map, Request.claim]

theorem requestAst_accept_spec (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧
      ∑ i, FStatistics.wReal r.demes i = 1 ∧
      (r.subpopulation : ℝ) = wMean (FStatistics.wReal r.demes)
        (fun i => Rhone.Statistics.FStatistics.hweHet (FStatistics.pReal r.demes i)) ∧
      (r.total : ℝ) = Rhone.Statistics.FStatistics.hweHet
        (wMean (FStatistics.wReal r.demes) (FStatistics.pReal r.demes)) ∧
      (r.fIS : ℝ) = Rhone.Statistics.FStatistics.fRatio (r.observed : ℝ) (r.subpopulation : ℝ) ∧
      (r.fST : ℝ) = Rhone.Statistics.FStatistics.fRatio (r.subpopulation : ℝ) (r.total : ℝ) ∧
      (r.fIT : ℝ) = Rhone.Statistics.FStatistics.fRatio (r.observed : ℝ) (r.total : ℝ) ∧
      r.deficit = r.total - r.subpopulation ∧
      (r.varianceForm : ℝ) =
        2 * wVar (FStatistics.wReal r.demes) (FStatistics.pReal r.demes) ∧
      r.varianceForm = r.deficit ∧ r.fSTWahlund = r.fST := by
  obtain ⟨r, hdecode, hvalid, hS, hT, hF, hD, hV, hW, -⟩ :=
    (requestAst_accept_iff doc count).mp haccept
  obtain ⟨hw, hS0, hT0, -⟩ := (Request.valid_iff r).mp hvalid
  have hF' : r.fIS = 1 - r.observed / r.subpopulation ∧
      r.fST = 1 - r.subpopulation / r.total ∧ r.fIT = 1 - r.observed / r.total := by
    have h := hF
    unfold FStatistics.fStatistics at h
    rw [ite_eq_right (not_or.mpr ⟨hS0, hT0⟩)] at h
    have h' := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    rw [hS, hT]
    exact ⟨h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩
  have hDform : r.deficit = FStatistics.pooledHet r.demes - FStatistics.meanHet r.demes := by
    have h := hD
    unfold FStatistics.wahlundDeficit at h
    rw [ite_eq_left hw] at h
    exact (Option.some.inj h).symm
  have hVform : r.varianceForm = 2 * FStatistics.weightedVariance r.demes := by
    have h := hV
    unfold FStatistics.wahlundVarianceForm at h
    rw [ite_eq_left hw] at h
    exact (Option.some.inj h).symm
  have hWform : r.fSTWahlund =
      2 * FStatistics.weightedVariance r.demes / FStatistics.pooledHet r.demes := by
    have h := hW
    unfold FStatistics.fStWahlund at h
    rw [ite_eq_left ⟨hw, hT0⟩] at h
    exact (Option.some.inj h).symm
  have hVD : r.varianceForm = r.deficit := by
    obtain ⟨q, hq1, hq2⟩ := FStatistics.wahlund_identity_exec r.demes hw
    rw [← Option.some.inj (hq1.symm.trans hD), ← Option.some.inj (hq2.symm.trans hV)]
  refine ⟨r, hdecode, (FStatistics.weightsNormalized_iff r.demes).mp hw, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hVD, ?_⟩
  · rw [hS]
    exact FStatistics.meanHet_eq r.demes
  · rw [hT]
    exact FStatistics.pooledHet_eq r.demes
  · rw [hF'.1]
    simp [Rhone.Statistics.FStatistics.fRatio]
  · rw [hF'.2.1]
    simp [Rhone.Statistics.FStatistics.fRatio]
  · rw [hF'.2.2]
    simp [Rhone.Statistics.FStatistics.fRatio]
  · rw [hDform, hS, hT]
  · obtain ⟨v, hv, hve⟩ := FStatistics.wahlundVarianceForm_eq r.demes hw
    rw [← Option.some.inj (hv.symm.trans hV)]
    exact hve
  · rw [hWform, hF'.2.1, ← hVform, hVD, hDform, hS, hT, sub_div, div_self hT0]

theorem requestAst_ofFormula (demes : List (Rat × Rat)) (observed : Rat)
    (hweights : FStatistics.weightsNormalized demes = true)
    (hsub : FStatistics.meanHet demes ≠ 0) (htotal : FStatistics.pooledHet demes ≠ 0)
    (hsize : demes.length ≤ 4096) :
    requestAst (encode (Request.ofFormula demes observed)) = .ok (stamp (true, 8)) := by
  have hvalid : (Request.ofFormula demes observed).valid = true :=
    (Request.valid_iff _).mpr ⟨hweights, hsub, htotal, hsize⟩
  have hF : FStatistics.fStatistics observed (FStatistics.meanHet demes)
      (FStatistics.pooledHet demes) = some (1 - observed / FStatistics.meanHet demes,
        1 - FStatistics.meanHet demes / FStatistics.pooledHet demes,
        1 - observed / FStatistics.pooledHet demes) := by
    unfold FStatistics.fStatistics
    rw [ite_eq_right (not_or.mpr ⟨hsub, htotal⟩)]
  obtain ⟨q, hq, -⟩ := FStatistics.wahlundDeficit_eq demes hweights
  obtain ⟨v, hv, -⟩ := FStatistics.wahlundVarianceForm_eq demes hweights
  obtain ⟨x, hx, -⟩ := FStatistics.fStWahlund_eq demes hweights htotal
  have hcheck : (Request.ofFormula demes observed).check = true :=
    (Request.check_iff _).mpr
      ⟨rfl, rfl, some_getD3 hF, some_getD hq, some_getD hv, some_getD hx⟩
  rw [requestAst_encode _ hvalid, hcheck]
  rfl

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.FStatisticsWire
