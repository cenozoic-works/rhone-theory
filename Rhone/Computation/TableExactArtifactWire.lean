/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.TableRelease
public import Rhone.Computation.GenericWire
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
/-! # Exact table artifact reader on the JSON abstract syntax tree -/

@[expose] public section
namespace Rhone.Computation.TableExactArtifactWire
open Lean

def strictRational (text : String) : Except String Rat := do
  let value ← RationalWire.decode text
  if text != RationalWire.strictPrint value then throw "noncanonical table fraction"
  return value

def strictField (doc : Json) (name : String) : Except String Rat :=
  doc.getObjValAs? String name >>= strictRational

def strictArray (doc : Json) (name : String) : Except String (Array Rat) := do
  let texts ← doc.getObjValAs? (Array String) name
  texts.mapM strictRational

def baselineModel : String :=
  "mutation=pim;selection=neutral;demography=stationary;sampling=contemporaneous;" ++
  "loci=2;structure=panmictic;adapter=autosomal"

structure Header where
  thetaA : Rat
  thetaB : Rat
  piA : Array Rat
  piB : Array Rat
  n : Nat
  keys : Array String
  configs : Array Rhone.Computation.Config
  gridKeys : Array String
  grid : Array Rat

def Header.typed (h : Header) : TableMatrix.Header h.piA.size h.piB.size :=
  ⟨h.thetaA, h.thetaB, GenericWire.pi h.piA, GenericWire.pi h.piB, h.n,
    h.configs.toList.map (GenericWire.toSpec h.piA.size h.piB.size), h.grid.toList⟩

def decodeHeader (doc : Json) : Except String Header := do
  GenericWire.fieldsAllowed doc ["schema", "release_status", "rhone_version", "model",
    "comparison_semantics", "source", "description", "n0", "KA", "KB", "thetaA", "thetaB",
    "piA", "piB", "rho_grid", "n_configs", "configs", "completed_rows", "values", "provenance"]
  let schema ← doc.getObjValAs? String "schema"
  if schema != "rhone-table-v3" then throw "unsupported exact artifact schema"
  let model ← doc.getObjValAs? String "model"
  if model != baselineModel then throw "unsupported exact table model"
  let semantics ← doc.getObjValAs? String "comparison_semantics"
  if semantics != "exact_fraction" then throw "unsupported table comparison semantics"
  let thetaA ← strictField doc "thetaA"
  let thetaB ← strictField doc "thetaB"
  let piA ← strictArray doc "piA"
  let piB ← strictArray doc "piB"
  let ka ← doc.getObjValAs? Nat "KA"
  let kb ← doc.getObjValAs? Nat "KB"
  if ka != piA.size then throw "table A alphabet mismatch"
  if kb != piB.size then throw "table B alphabet mismatch"
  let n ← doc.getObjValAs? Nat "n0"
  let keys ← doc.getObjValAs? (Array String) "configs"
  let configs ← keys.mapM (fun key => parseConfig key ka kb)
  let count ← doc.getObjValAs? Nat "n_configs"
  if count != keys.size then throw "table configuration count mismatch"
  let gridKeys ← doc.getObjValAs? (Array String) "rho_grid"
  let grid ← gridKeys.mapM strictRational
  let completed ← doc.getObjValAs? Nat "completed_rows"
  if completed != grid.size then throw "partial table artifact"
  return ⟨thetaA, thetaB, piA, piB, n, keys, configs, gridKeys, grid⟩

def readValues (h : Header) (doc : Json) : Except String (Array (Array Rat)) := do
  let values ← doc.getObjVal? "values"
  GenericWire.fieldsAllowed values h.gridKeys.toList
  h.gridKeys.mapM fun gridKey => do
    let row ← values.getObjVal? gridKey
    GenericWire.fieldsAllowed row h.keys.toList
    h.keys.mapM fun key => strictField row key

def readCertificates (h : Header) (doc : Json) :
    Except String (Array (Array (Rhone.Computation.Config × Rat))) := do
  let certificates ← doc.getArr?
  if certificates.size != h.grid.size then throw "table certificate count mismatch"
  certificates.mapM fun row => do
    let entries ← row.getArr?
    entries.mapM (GenericWire.entry h.piA.size h.piB.size)

structure Request where
  header : Header
  values : Array (Array Rat)
  certificates : Array (Array (Rhone.Computation.Config × Rat))

def Request.rows (r : Request) :
    List (TableMatrix.Row r.header.piA.size r.header.piB.size) :=
  ((r.header.grid.toList.zip r.values.toList).zip r.certificates.toList).map
    (fun ((rho, values), certificate) =>
      ⟨rho, values.toList, certificate.toList.map
        (fun row => (GenericWire.toSpec r.header.piA.size r.header.piB.size row.1, row.2))⟩)

def Request.accepted (r : Request) : Bool :=
  (r.values.size == r.header.grid.size && r.certificates.size == r.header.grid.size) &&
    TableRelease.accepted r.header.typed r.header.n r.rows

def decode (doc : Json) : Except String Request := do
  GenericWire.fieldsAllowed doc ["op", "table", "certificates", "provenance", "rhone_version"]
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table_file_exact" then throw "unsupported exact table operation"
  let table ← doc.getObjVal? "table"
  let header ← decodeHeader table
  let values ← readValues header table
  let certificates ← doc.getObjVal? "certificates" >>= readCertificates header
  return ⟨header, values, certificates⟩

def checkRequest (doc : Json) : Except String Bool := do
  let r ← decode doc
  return r.accepted

lemma Request.accepted_source {r : Request} (h : r.accepted = true) :
    TableRelease.accepted r.header.typed r.header.n r.rows = true := by
  simp only [Request.accepted, Bool.and_eq_true] at h
  exact h.2

lemma Request.accepted_probability {r : Request} (h : r.accepted = true)
    (row : TableMatrix.Row r.header.piA.size r.header.piB.size) (hr : row ∈ r.rows) :
    List.Forall₂ (fun (ξ : Rhone.LinearAlgebra.Recursion.Config r.header.piA.size r.header.piB.size)
      (v : Rat) => (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.header.thetaA : Real) (r.header.thetaB : Real) (row.rho : Real)
        (fun i => (GenericWire.pi r.header.piA i : Real))
        (fun j => (GenericWire.pi r.header.piB j : Real)) ξ)
      r.header.typed.configs row.values :=
  TableRelease.accepted_probability (Request.accepted_source h) row hr

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

lemma strictRational_original (text : String) (value : Rat)
    (h : strictRational text = .ok value) :
    RationalWire.decode text = .ok value ∧ text = RationalWire.strictPrint value := by
  unfold strictRational at h
  refine of_bind_ok h fun v hv h => ?_
  by_cases he : text = RationalWire.strictPrint v
  · simp only [he, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain rfl := Except.ok.inj h
    exact ⟨hv, he⟩
  · simp [he] at h

def Header.original (doc : Json) (h : Header) : Prop :=
  doc.getObjValAs? String "schema" = .ok "rhone-table-v3" ∧
  doc.getObjValAs? String "model" = .ok baselineModel ∧
  doc.getObjValAs? String "comparison_semantics" = .ok "exact_fraction" ∧
  strictField doc "thetaA" = .ok h.thetaA ∧ strictField doc "thetaB" = .ok h.thetaB ∧
  strictArray doc "piA" = .ok h.piA ∧ strictArray doc "piB" = .ok h.piB ∧
  doc.getObjValAs? Nat "KA" = .ok h.piA.size ∧
  doc.getObjValAs? Nat "KB" = .ok h.piB.size ∧
  doc.getObjValAs? Nat "n0" = .ok h.n ∧
  doc.getObjValAs? (Array String) "configs" = .ok h.keys ∧
  h.keys.mapM (fun key => parseConfig key h.piA.size h.piB.size) = .ok h.configs ∧
  doc.getObjValAs? Nat "n_configs" = .ok h.keys.size ∧
  doc.getObjValAs? (Array String) "rho_grid" = .ok h.gridKeys ∧
  h.gridKeys.mapM strictRational = .ok h.grid ∧
  doc.getObjValAs? Nat "completed_rows" = .ok h.grid.size

lemma decodeHeader_original (doc : Json) (header : Header)
    (h : decodeHeader doc = .ok header) : header.original doc := by
  unfold decodeHeader at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun schema hs h => ?_
  by_cases hschema : schema = "rhone-table-v3"
  · simp only [hschema, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine of_bind_ok h fun model hm h => ?_
    by_cases hmodel : model = baselineModel
    · simp only [hmodel, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      refine of_bind_ok h fun semantics hsem h => ?_
      by_cases hsemantic : semantics = "exact_fraction"
      · simp only [hsemantic, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
        refine of_bind_ok h fun thetaA ha h => ?_
        refine of_bind_ok h fun thetaB hb h => ?_
        refine of_bind_ok h fun piA hpa h => ?_
        refine of_bind_ok h fun piB hpb h => ?_
        refine of_bind_ok h fun ka hka h => ?_
        refine of_bind_ok h fun kb hkb h => ?_
        by_cases hkaeq : ka = piA.size
        · simp only [hkaeq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hkbeq : kb = piB.size
          · simp only [hkbeq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
            refine of_bind_ok h fun n hn h => ?_
            refine of_bind_ok h fun keys hkeys h => ?_
            refine of_bind_ok h fun configs hconfigs h => ?_
            refine of_bind_ok h fun count hcount h => ?_
            by_cases hcountEq : count = keys.size
            · simp only [hcountEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
              refine of_bind_ok h fun gridKeys hgridKeys h => ?_
              refine of_bind_ok h fun grid hgrid h => ?_
              refine of_bind_ok h fun completed hc h => ?_
              by_cases hcomplete : completed = grid.size
              · simp only [hcomplete, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
                obtain rfl := Except.ok.inj h
                exact ⟨hschema ▸ hs, hmodel ▸ hm, hsemantic ▸ hsem, ha, hb, hpa, hpb,
                  hkaeq ▸ hka, hkbeq ▸ hkb, hn, hkeys, hconfigs, hcountEq ▸ hcount,
                  hgridKeys, hgrid, hcomplete ▸ hc⟩
              · simp [hcomplete] at h
            · simp [hcountEq] at h
          · simp [hkbeq] at h
        · simp [hkaeq] at h
      · simp [hsemantic] at h
    · simp [hmodel] at h
  · simp [hschema] at h

lemma decode_original (doc : Json) (r : Request) (h : decode doc = .ok r) :
    ∃ table : Json, doc.getObjValAs? String "op" = .ok "check_table_file_exact" ∧
      doc.getObjVal? "table" = .ok table ∧ decodeHeader table = .ok r.header ∧
      readValues r.header table = .ok r.values ∧
      (doc.getObjVal? "certificates" >>= readCertificates r.header) = .ok r.certificates := by
  unfold decode at h
  refine of_bind_ok h fun _ _ h => ?_
  refine of_bind_ok h fun op hop h => ?_
  by_cases he : op = "check_table_file_exact"
  · simp only [he, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine of_bind_ok h fun table ht h => ?_
    refine of_bind_ok h fun header hh h => ?_
    refine of_bind_ok h fun values hv h => ?_
    refine of_bind_ok h fun certificates hc h => ?_
    obtain rfl := Except.ok.inj h
    exact ⟨table, he ▸ hop, ht, hh, hv, hc⟩
  · simp [he] at h

lemma checkRequest_original (doc : Json) (h : checkRequest doc = .ok true) :
    ∃ r : Request, decode doc = .ok r ∧ r.accepted = true := by
  unfold checkRequest at h
  refine of_bind_ok h fun r hr h => ?_
  exact ⟨r, hr, Except.ok.inj h⟩

def Header.agrees (source output : Header) : Bool := decide (
  source.thetaA = output.thetaA ∧ source.thetaB = output.thetaB ∧
  source.piA = output.piA ∧ source.piB = output.piB ∧ source.n = output.n ∧
  source.keys = output.keys ∧ source.gridKeys = output.gridKeys ∧ source.grid = output.grid)

def checkRequestAt (sourceDoc doc : Json) : Except String Bool := do
  let source ← decodeHeader sourceDoc
  let r ← decode doc
  return source.agrees r.header && r.accepted

lemma checkRequestAt_original (sourceDoc doc : Json)
    (h : checkRequestAt sourceDoc doc = .ok true) :
    ∃ source : Header, ∃ r : Request,
      decodeHeader sourceDoc = .ok source ∧ decode doc = .ok r ∧
      source.agrees r.header = true ∧ r.accepted = true := by
  unfold checkRequestAt at h
  refine of_bind_ok h fun source hs h => ?_
  refine of_bind_ok h fun r hr h => ?_
  have he := Except.ok.inj h
  simp only [Bool.and_eq_true] at he
  exact ⟨source, r, hs, hr, he⟩

lemma Header.agrees_fields (source output : Header) (h : source.agrees output = true) :
    source.thetaA = output.thetaA ∧ source.thetaB = output.thetaB ∧
    source.piA = output.piA ∧ source.piB = output.piB ∧ source.n = output.n ∧
    source.keys = output.keys ∧ source.gridKeys = output.gridKeys ∧ source.grid = output.grid := by
  simpa only [Header.agrees, decide_eq_true_eq] using h

lemma readValues_original (header : Header) (doc : Json) (rows : Array (Array Rat))
    (h : readValues header doc = .ok rows) :
    ∃ values : Json, doc.getObjVal? "values" = .ok values ∧
      header.gridKeys.mapM (fun gridKey => do
        let row ← values.getObjVal? gridKey
        GenericWire.fieldsAllowed row header.keys.toList
        header.keys.mapM fun key => strictField row key) = .ok rows := by
  unfold readValues at h
  refine of_bind_ok h fun values hv h => ?_
  refine of_bind_ok h fun _ _ h => ?_
  exact ⟨values, hv, h⟩

lemma list_mapM_original {α β : Type} (f : α → Except String β)
    (xs : List α) (ys : List β) (h : xs.mapM f = .ok ys) :
    List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure_def, Except.ok.injEq] at h
    subst ys
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    refine of_bind_ok h fun y hy h => ?_
    refine of_bind_ok h fun tail ht h => ?_
    obtain rfl := Except.ok.inj h
    exact .cons hy (ih tail ht)

lemma array_mapM_original {α β : Type} (f : α → Except String β)
    (xs : Array α) (ys : Array β) (h : xs.mapM f = .ok ys) :
    List.Forall₂ (fun x y => f x = .ok y) xs.toList ys.toList := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases ht : xs.toList.mapM f with
  | error e => simp [ht] at h
  | ok tail =>
    have he : tail.toArray = ys := by simpa [ht] using h
    rw [← he, List.toList_toArray]
    exact list_mapM_original f xs.toList tail ht

lemma readValues_cells (header : Header) (doc : Json) (rows : Array (Array Rat))
    (h : readValues header doc = .ok rows) :
    ∃ values : Json, doc.getObjVal? "values" = .ok values ∧
      List.Forall₂ (fun gridKey rowValues => ∃ row : Json,
        values.getObjVal? gridKey = .ok row ∧
        List.Forall₂ (fun key value => strictField row key = .ok value)
          header.keys.toList rowValues.toList) header.gridKeys.toList rows.toList := by
  obtain ⟨values, hv, hrows⟩ := readValues_original header doc rows h
  refine ⟨values, hv, ?_⟩
  apply (array_mapM_original _ _ _ hrows).imp
  intro gridKey rowValues hr
  refine of_bind_ok hr fun row hrow hr => ?_
  refine of_bind_ok hr fun _ _ hr => ?_
  exact ⟨row, hrow, array_mapM_original _ _ _ hr⟩

lemma Request.accepted_lengths {r : Request} (h : r.accepted = true) :
    r.values.size = r.header.grid.size ∧ r.certificates.size = r.header.grid.size := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

lemma Request.rows_values {r : Request} (h : r.accepted = true) :
    r.rows.map TableMatrix.Row.values = r.values.toList.map Array.toList := by
  have hl := Request.accepted_lengths h
  have hout : ((r.header.grid.toList.zip r.values.toList).zip r.certificates.toList).map
      Prod.fst = r.header.grid.toList.zip r.values.toList := by
    apply List.map_fst_zip
    simp only [List.length_zip, Array.length_toList]
    rw [hl.1, hl.2]
    simp
  have hin : (r.header.grid.toList.zip r.values.toList).map Prod.snd = r.values.toList := by
    apply List.map_snd_zip
    simpa only [Array.length_toList, hl.1] using le_refl r.header.grid.size
  calc
    r.rows.map TableMatrix.Row.values =
        (((r.header.grid.toList.zip r.values.toList).zip r.certificates.toList).map
          Prod.fst).map (fun row => row.2.toList) := by
      simp [Request.rows, List.map_map]
    _ = (r.header.grid.toList.zip r.values.toList).map (fun row => row.2.toList) := by
      rw [hout]
    _ = r.values.toList.map Array.toList := by
      have he := congrArg (List.map Array.toList) hin
      simpa only [List.map_map, Function.comp_def] using he

lemma Request.input_values_probability {r : Request} (h : r.accepted = true)
    (values : Array Rat) (hv : values ∈ r.values.toList) :
    ∃ rho ∈ r.header.grid.toList,
      List.Forall₂ (fun
          (ξ : Rhone.LinearAlgebra.Recursion.Config r.header.piA.size r.header.piB.size)
        (v : Rat) => (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
          (r.header.thetaA : Real) (r.header.thetaB : Real) (rho : Real)
          (fun i => (GenericWire.pi r.header.piA i : Real))
          (fun j => (GenericWire.pi r.header.piB j : Real)) ξ)
        r.header.typed.configs values.toList := by
  have hm : values.toList ∈ r.rows.map TableMatrix.Row.values := by
    rw [Request.rows_values h]
    exact List.mem_map.mpr ⟨values, hv, rfl⟩
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  have hgrid := TableMatrix.accepted_grid r.header.typed r.rows
    (TableRelease.accepted_matrix (Request.accepted_source h))
  have hmem : row.rho ∈ r.rows.map TableMatrix.Row.rho := List.mem_map.mpr ⟨row, hr, rfl⟩
  rw [hgrid] at hmem
  refine ⟨row.rho, hmem, ?_⟩
  rw [← he]
  exact Request.accepted_probability h row hr

lemma zip3_forall2 {α β γ : Type} (P : α → β → Prop)
    (xs : List α) (ys : List β) (zs : List γ)
    (hxy : xs.length = ys.length) (hxz : xs.length = zs.length)
    (hall : ∀ triple ∈ (xs.zip ys).zip zs, P triple.1.1 triple.1.2) :
    List.Forall₂ P xs ys := by
  induction xs generalizing ys zs with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hxy.symm
    subst ys
    exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp at hxy
    | cons y ys =>
      cases zs with
      | nil => simp at hxz
      | cons z zs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hxy hxz
        refine .cons (hall ((x, y), z) (by simp)) (ih ys zs hxy hxz ?_)
        intro triple ht
        exact hall triple (by simp [ht])

lemma Request.ordered_values_probability {r : Request} (h : r.accepted = true) :
    List.Forall₂ (fun (rho : Rat) (values : Array Rat) =>
      List.Forall₂ (fun
          (ξ : Rhone.LinearAlgebra.Recursion.Config r.header.piA.size r.header.piB.size)
        (v : Rat) => (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
          (r.header.thetaA : Real) (r.header.thetaB : Real) (rho : Real)
          (fun i => (GenericWire.pi r.header.piA i : Real))
          (fun j => (GenericWire.pi r.header.piB j : Real)) ξ)
        r.header.typed.configs values.toList) r.header.grid.toList r.values.toList := by
  have hl := Request.accepted_lengths h
  apply zip3_forall2 _ _ _ r.certificates.toList
    (by simpa only [Array.length_toList] using hl.1.symm)
    (by simpa only [Array.length_toList] using hl.2.symm)
  rintro ⟨⟨rho, values⟩, certificate⟩ ht
  let row : TableMatrix.Row r.header.piA.size r.header.piB.size :=
    ⟨rho, values.toList, certificate.toList.map
      (fun cell => (GenericWire.toSpec r.header.piA.size r.header.piB.size cell.1, cell.2))⟩
  have hr : row ∈ r.rows := List.mem_map.mpr ⟨((rho, values), certificate), ht, rfl⟩
  exact Request.accepted_probability h row hr

def requestAt (sourceLine line : String) : Except String Bool := do
  let sourceDoc ← Json.parse sourceLine
  let doc ← Json.parse line
  checkRequestAt sourceDoc doc

lemma requestAt_original (sourceLine line : String)
    (h : requestAt sourceLine line = .ok true) :
    ∃ sourceDoc doc : Json, Json.parse sourceLine = .ok sourceDoc ∧
      Json.parse line = .ok doc ∧ checkRequestAt sourceDoc doc = .ok true := by
  unfold requestAt at h
  refine of_bind_ok h fun sourceDoc hs h => ?_
  refine of_bind_ok h fun doc hd h => ?_
  exact ⟨sourceDoc, doc, hs, hd, h⟩

lemma strictField_original (doc : Json) (key : String) (value : Rat)
    (h : strictField doc key = .ok value) :
    doc.getObjValAs? String key = .ok (RationalWire.strictPrint value) ∧
      RationalWire.decode (RationalWire.strictPrint value) = .ok value := by
  unfold strictField at h
  refine of_bind_ok h fun text ht h => ?_
  obtain ⟨hv, he⟩ := strictRational_original text value h
  exact ⟨he ▸ ht, he ▸ hv⟩

lemma agreed_decoded_configs {source output : Header} {sourceDoc outputDoc : Json}
    (hs : source.original sourceDoc) (ho : output.original outputDoc)
    (ha : source.agrees output = true) : source.configs = output.configs := by
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, hsc, _, _, _, _⟩
  rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, hoc, _, _, _, _⟩
  rcases Header.agrees_fields source output ha with ⟨_, _, hpa, hpb, _, hkeys, _, _⟩
  have he : source.keys.mapM (fun key =>
      parseConfig key source.piA.size source.piB.size) = .ok output.configs := by
    simpa only [← hpa, ← hpb, ← hkeys] using hoc
  exact Except.ok.inj (hsc.symm.trans he)

lemma agreed_decoded_header {source output : Header} {sourceDoc outputDoc : Json}
    (hs : source.original sourceDoc) (ho : output.original outputDoc)
    (ha : source.agrees output = true) : source = output := by
  have hc := agreed_decoded_configs hs ho ha
  have hf := Header.agrees_fields source output ha
  cases source with
  | mk a b pa pb n keys configs gridKeys grid =>
    cases output with
    | mk a' b' pa' pb' n' keys' configs' gridKeys' grid' =>
      change configs = configs' at hc
      change a = a' ∧ b = b' ∧ pa = pa' ∧ pb = pb' ∧ n = n' ∧ keys = keys' ∧
        gridKeys = gridKeys' ∧ grid = grid' at hf
      rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases hc
      rfl

lemma checkRequestAt_header {sourceDoc doc : Json}
    (h : checkRequestAt sourceDoc doc = .ok true) :
    ∃ source : Header, ∃ r : Request,
      decodeHeader sourceDoc = .ok source ∧ decode doc = .ok r ∧
      source = r.header ∧ r.accepted = true := by
  obtain ⟨source, r, hs, hr, ha, haccept⟩ := checkRequestAt_original sourceDoc doc h
  obtain ⟨table, _, _, ht, _, _⟩ := decode_original doc r hr
  exact ⟨source, r, hs, hr,
    agreed_decoded_header (decodeHeader_original sourceDoc source hs)
      (decodeHeader_original table r.header ht) ha, haccept⟩

end Rhone.Computation.TableExactArtifactWire
