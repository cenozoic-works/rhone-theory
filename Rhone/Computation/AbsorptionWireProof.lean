/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.AbsorptionWire
public import Rhone.Computation.AbsorptionProof
public import Rhone.Computation.RationalWirePrintProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Fidelity of the absorption report reader -/

@[expose] public section
namespace Rhone.Computation.AbsorptionWire
open Lean MarkovChain MeasureTheory Absorption

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
    r.valid = true ↔ 1 ≤ r.geneCopies ∧ r.geneCopies ≤ 16 ∧ r.initialCount ≤ r.geneCopies ∧
      (r.moran = true → 0 < r.fitness) ∧ r.provenance.trimAscii.toString.isEmpty = false ∧
      r.scalar = r.table.getD r.initialCount 0 := by
  unfold Request.valid
  rw [decide_eq_true_iff]

theorem stamp_injective : Function.Injective stamp := by
  intro first second h
  have hd : ∀ d : Bool × Nat, ([("schema", toJson "rhone-compute-absorption-check-v1"),
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

private theorem rowEntry_encodeEntry (value : Rat) :
    rowEntry (encodeEntry value) = .ok value :=
  RationalWire.decode_strictPrint value

private theorem list_row_encode (values : List Rat) :
    (values.map encodeEntry).mapM rowEntry = .ok values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, rowEntry_encodeEntry, ih]

theorem ratArray_encode (values : Array Rat) :
    ratArray (encodeArray values) = .ok values := by
  have hl := list_row_encode values.toList
  unfold ratArray encodeArray
  change (Except.ok (values.map encodeEntry) : Except String (Array Json)) >>= _ = _
  rw [ok_bind, Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

private theorem list_kernel_encode (rows : List (Array Rat)) :
    (rows.map encodeArray).mapM ratArray = .ok rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [List.mapM_cons, ratArray_encode, ih]

theorem kernel_encode (kernel : Array (Array Rat)) :
    (kernel.map encodeArray).mapM ratArray = .ok kernel := by
  have hl := list_kernel_encode kernel.toList
  rw [Array.mapM_eq_mapM_toList, Array.toList_map, hl]
  simp

private theorem modelFields_encode (r : Request) (hcanonical : r.Canonical) :
    modelFields (encode r) (if r.moran then "moran" else "wright-fisher") =
      .ok (r.moran, r.fitness) := by
  obtain ⟨moran, n, i, fitness, provenance, kernel, table, scalar⟩ := r
  cases moran with
  | false =>
    have hone : fitness = 1 := hcanonical rfl
    subst hone
    have hfitness := encode_getObjVal (r := ⟨false, n, i, 1, provenance, kernel, table,
      scalar⟩) (name := "relative_fitness") (value := .null) (by simp [requestFields])
    have hunit := getStr_of (encode_getObjVal (r := ⟨false, n, i, 1, provenance, kernel,
      table, scalar⟩) (name := "time_unit") (value := .str "generation")
      (by simp [requestFields]))
    simp [modelFields, hfitness, hunit]
  | true =>
    have hfitness := rat_of (encode_getObjVal (r := ⟨true, n, i, fitness, provenance, kernel,
      table, scalar⟩) (name := "relative_fitness") (value := encodeEntry fitness)
      (by simp [requestFields]))
    have hunit := getStr_of (encode_getObjVal (r := ⟨true, n, i, fitness, provenance, kernel,
      table, scalar⟩) (name := "time_unit") (value := .str "birth-death-event")
      (by simp [requestFields]))
    simp [modelFields, hfitness, hunit]

theorem decode_encode (r : Request) (hcanonical : r.Canonical) :
    decode (encode r) = .ok r := by
  have hschema := getStr_of (encode_getObjVal (r := r) (name := "schema")
    (value := .str "rhone-drift-absorption-v1") (by simp [requestFields, toJson]))
  have hsemantics := getStr_of (encode_getObjVal (r := r) (name := "comparison_semantics")
    (value := .str "exact_fraction") (by simp [requestFields, toJson]))
  have hscope := getStr_of (encode_getObjVal (r := r) (name := "scope")
    (value := .str "complete-supplied-discrete-zero-mutation-absorption-table")
    (by simp [requestFields, toJson]))
  have hmodel := getStr_of (encode_getObjVal (r := r) (name := "model")
    (value := .str (if r.moran then "moran" else "wright-fisher")) (by simp [requestFields]))
  have hn := getNat_of (encode_getObjVal (r := r) (name := "gene_copies")
    (value := toJson r.geneCopies) (by simp [requestFields]))
  have hi := getNat_of (encode_getObjVal (r := r) (name := "initial_count")
    (value := toJson r.initialCount) (by simp [requestFields]))
  have hprovenance := getStr_of (encode_getObjVal (r := r) (name := "parameter_provenance")
    (value := .str r.provenance) (by simp [requestFields]))
  have htable : ((encode r).getObjVal? "mean_absorption_times").bind ratArray =
      .ok r.table := by
    rw [encode_getObjVal (r := r) (name := "mean_absorption_times")
      (value := encodeArray r.table) (by simp [requestFields])]
    exact ratArray_encode r.table
  have hrows : ((encode r).getObjVal? "transition_kernel").bind Json.getArr? =
      .ok (r.kernel.map encodeArray) := by
    rw [encode_getObjVal (r := r) (name := "transition_kernel")
      (value := .arr (r.kernel.map encodeArray)) (by simp [requestFields])]
    rfl
  have hscalar := rat_of (encode_getObjVal (r := r) (name := "mean_absorption_time")
    (value := encodeEntry r.scalar) (by simp [requestFields]))
  have hfields := modelFields_encode r hcanonical
  have hkernel := kernel_encode r.kernel
  simp [decode, hschema, hsemantics, hscope, hmodel, hn, hi, hprovenance, htable, hrows,
    hkernel, hscalar, hfields]

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

theorem decode_canonical (doc : Json) (r : Request) (hdecode : decode doc = .ok r) :
    r.Canonical := by
  unfold decode at hdecode
  refine of_bind_ok hdecode fun schema _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun semantics _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun scope _ h => ?_
  replace h := of_guard_ok h
  refine of_bind_ok h fun n _ h => ?_
  refine of_bind_ok h fun i _ h => ?_
  refine of_bind_ok h fun provenance _ h => ?_
  refine of_bind_ok h fun table _ h => ?_
  refine of_bind_ok h fun rows _ h => ?_
  refine of_bind_ok h fun kernel _ h => ?_
  refine of_bind_ok h fun scalar _ h => ?_
  refine of_bind_ok h fun model _ h => ?_
  refine of_bind_ok h fun fields hfields h => ?_
  obtain rfl := Except.ok.inj h
  exact modelFields_fitness doc model fields hfields

private theorem decision_encode (r : Request) (hcanonical : r.Canonical) :
    decision (encode r) = if r.valid then .ok (r.check, r.claimed)
      else .error "unsupported absorption request domain" := by
  simp [decision, decode_encode r hcanonical]

theorem requestAst_encode (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = true) :
    requestAst (encode r) = .ok (stamp (r.check, r.claimed)) := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_encode_outside (r : Request) (hcanonical : r.Canonical)
    (hvalid : r.valid = false) :
    requestAst (encode r) = .error "unsupported absorption request domain" := by
  simp [requestAst, decision_encode r hcanonical, hvalid, Except.map]

theorem requestAst_ok (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      out = stamp (r.check, r.claimed) ∧ requestAst (encode r) = .ok out := by
  unfold requestAst decision at hok
  cases hdecode : decode doc with
  | error message => simp [hdecode, Except.map] at hok
  | ok r =>
    have hcanonical := decode_canonical doc r hdecode
    cases hvalid : r.valid with
    | false => simp [hdecode, hvalid, Except.map] at hok
    | true =>
      have hout : out = stamp (r.check, r.claimed) := by
        simpa [hdecode, hvalid, Except.map] using hok.symm
      exact ⟨r, rfl, hcanonical, hvalid, hout, hout ▸ requestAst_encode r hcanonical hvalid⟩

private theorem check_true (r : Request) (h : r.check = true) :
    (r.moran = false → r.kernel = wfKernel r.geneCopies ∧ checkWf r.geneCopies r.table = true) ∧
    (r.moran = true → r.kernel = moranKernel r.geneCopies r.fitness ∧
      checkMoran r.geneCopies r.fitness r.table = true) := by
  constructor
  · intro hmodel
    simp only [Request.check, hmodel, Bool.false_eq_true, ite_false, checkWfReport,
      Bool.and_eq_true, decide_eq_true_eq] at h
    exact h
  · intro hmodel
    simp only [Request.check, hmodel, ite_true, checkMoranReport, Bool.and_eq_true,
      decide_eq_true_eq] at h
    exact h

theorem requestAst_accept_sound (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ r.Canonical ∧ r.valid = true ∧
      (r.moran = false → r.kernel = Absorption.wfKernel r.geneCopies ∧
        Absorption.checkWf r.geneCopies r.table = true) ∧
      (r.moran = true → r.kernel = Absorption.moranKernel r.geneCopies r.fitness ∧
        Absorption.checkMoran r.geneCopies r.fitness r.table = true) ∧
      count = r.claimed ∧ requestAst (encode r) = .ok (stamp (true, count)) := by
  obtain ⟨r, hdecode, hcanonical, hvalid, hout, hencode⟩ := requestAst_ok doc _ haccept
  have hpair := stamp_injective hout
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hcheck, hcount⟩ := hpair
  obtain ⟨hwf, hmoran⟩ := check_true r hcheck.symm
  exact ⟨r, hdecode, hcanonical, hvalid, hwf, hmoran, hcount, hencode⟩

theorem requestAst_encode_accept_sound (r : Request) (hcanonical : r.Canonical)
    (count : Nat) (haccept : requestAst (encode r) = .ok (stamp (true, count))) :
    r.valid = true ∧
      (r.moran = false → r.kernel = Absorption.wfKernel r.geneCopies ∧
        Absorption.checkWf r.geneCopies r.table = true) ∧
      (r.moran = true → r.kernel = Absorption.moranKernel r.geneCopies r.fitness ∧
        Absorption.checkMoran r.geneCopies r.fitness r.table = true) ∧
      count = r.claimed := by
  obtain ⟨decoded, hdecode, -, hvalid, hwf, hmoran, hcount, -⟩ :=
    requestAst_accept_sound (encode r) count haccept
  rw [decode_encode r hcanonical] at hdecode
  cases hdecode
  exact ⟨hvalid, hwf, hmoran, hcount⟩

theorem requestAst_accept_request (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 < r.geneCopies ∧
      (r.moran = false →
        Absorption.checkWfReport r.geneCopies r.kernel r.table = true) ∧
      (r.moran = true → 0 < (r.fitness : Real) ∧
        Absorption.checkMoranReport r.geneCopies r.fitness r.kernel r.table = true) := by
  obtain ⟨r, hdecode, -, hvalid, hwf, hmoran, -⟩ := requestAst_accept_sound doc count haccept
  obtain ⟨hlower, -, -, hfitness, -⟩ := (Request.valid_iff r).mp hvalid
  refine ⟨r, hdecode, hlower, ?_, ?_⟩
  · intro hmodel
    obtain ⟨hkernel, htable⟩ := hwf hmodel
    simp [checkWfReport, hkernel, htable]
  · intro hmodel
    obtain ⟨hkernel, htable⟩ := hmoran hmodel
    exact ⟨Rat.cast_pos.mpr (hfitness hmodel), by simp [checkMoranReport, hkernel, htable]⟩

theorem requestAst_accept_hitTime (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ r : Request, decode doc = .ok r ∧ 0 < r.geneCopies ∧
      (r.moran = false → ∀ i : Fin (r.geneCopies + 1),
        ∫⁻ ω, (hitTime (fixationBoundary r.geneCopies) ω : ENNReal)
          ∂(wfChain r.geneCopies).pathLaw i = ENNReal.ofReal (r.table.getD i 0 : Real)) ∧
      (r.moran = true → ∃ hr : 0 < (r.fitness : Real), ∀ i : Fin (r.geneCopies + 1),
        ∫⁻ ω, (hitTime (fixationBoundary r.geneCopies) ω : ENNReal)
          ∂(moranChain r.geneCopies (r.fitness : Real) hr).pathLaw i =
            ENNReal.ofReal (r.table.getD i 0 : Real)) := by
  obtain ⟨r, hdecode, -, hvalid, hwf, hmoran, -⟩ := requestAst_accept_sound doc count haccept
  obtain ⟨hlower, -, -, hfitness, -⟩ := (Request.valid_iff r).mp hvalid
  refine ⟨r, hdecode, hlower, ?_, ?_⟩
  · intro hmodel
    exact fun i => checkWf_lintegral_hitTime r.geneCopies hlower r.table (hwf hmodel).2 i
  · intro hmodel
    have hr : 0 < (r.fitness : Real) := Rat.cast_pos.mpr (hfitness hmodel)
    exact ⟨hr, fun i =>
      checkMoran_lintegral_hitTime r.geneCopies hlower r.fitness hr r.table
        (hmoran hmodel).2 i⟩

theorem requestAst_decode_error (doc : Json) (message : String)
    (herror : decode doc = .error message) : requestAst doc = .error message := by
  simp [requestAst, decision, herror, Except.map]

end Rhone.Computation.AbsorptionWire
