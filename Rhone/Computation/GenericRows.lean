/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.GenericClosure
public import Mathlib.Data.List.Dedup
/-! # General-allele exact row checking -/

@[expose] public section
namespace Rhone.Computation.GenericRows
open LinearAlgebra.Recursion

def same {KA KB : Nat} (x y : Config KA KB) : Bool :=
  decide (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c)

lemma same_true_iff {KA KB : Nat} (x y : Config KA KB) : same x y = true ↔ x = y := by
  simp only [same, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact Config.ext ha hb hc
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩

instance configDecidableEq {KA KB : Nat} : DecidableEq (Config KA KB) := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c) (by
    constructor
    · rintro ⟨ha, hb, hc⟩
      exact Config.ext ha hb hc
    · intro h
      cases h
      exact ⟨rfl, rfl, rfl⟩)

def keys (KA KB N : Nat) : List (Config KA KB) := (GenericClosure.configs KA KB N).dedup

lemma mem_keys_iff {KA KB N : Nat} (ξ : Config KA KB) :
    ξ ∈ keys KA KB N ↔ CheckerSpec.InClosure N ξ := by
  simp only [keys, List.mem_dedup, GenericClosure.mem_configs_iff]

def uniqueKeys {KA KB : Nat} (rows : List (Config KA KB × Rat)) : Bool :=
  decide ((rows.map Prod.fst).Nodup)

def value {KA KB : Nat} (rows : List (Config KA KB × Rat)) (ξ : Config KA KB) : Rat :=
  match rows.find? (fun row => same row.1 ξ) with
  | some row => row.2
  | none => 0

def present {KA KB : Nat} (rows : List (Config KA KB × Rat)) (ξ : Config KA KB) : Bool :=
  rows.any (fun row => same row.1 ξ)

def noConflicts {KA KB : Nat} (rows : List (Config KA KB × Rat)) : Bool :=
  rows.all (fun row => decide (value rows row.1 = row.2))

lemma noConflicts_sound {KA KB : Nat} {rows : List (Config KA KB × Rat)}
    (h : noConflicts rows = true) (row : Config KA KB × Rat) (hr : row ∈ rows) :
    value rows row.1 = row.2 := by
  simp only [noConflicts, List.all_eq_true, decide_eq_true_eq] at h
  exact h row hr

lemma value_map {KA KB : Nat} (xs : List (Config KA KB))
    (f : Config KA KB → Rat) (ξ : Config KA KB) (hξ : ξ ∈ xs) :
    value (xs.map (fun η => (η, f η))) ξ = f ξ := by
  unfold value
  cases hr : (xs.map (fun η => (η, f η))).find? (fun row => same row.1 ξ) with
  | none =>
    have hnone := List.find?_eq_none.mp hr
    have hrow : (ξ, f ξ) ∈ xs.map (fun η => (η, f η)) := List.mem_map.mpr ⟨ξ, hξ, rfl⟩
    have hbad := hnone (ξ, f ξ) hrow
    have hsame : same ξ ξ = true := (same_true_iff _ _).mpr rfl
    simp [hsame] at hbad
  | some row =>
    have hsame : same row.1 ξ = true :=
      List.find?_some (p := fun row : Config KA KB × Rat => same row.1 ξ) hr
    have heq := (same_true_iff _ _).mp hsame
    have hrow := List.mem_of_find?_eq_some hr
    obtain ⟨η, _, hη⟩ := List.mem_map.mp hrow
    have hfst : η = ξ := by simpa [← hη] using heq
    simp [← hη, hfst]

def check {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat) (N : Nat)
    (rows : List (Config KA KB × Rat)) : Bool :=
  rows.all (fun row => decide (Rhone.Computation.CheckerSpec.InClosure N row.1)) &&
  (GenericClosure.configs KA KB N).all (present rows) &&
  (uniqueKeys rows && noConflicts rows) &&
  GenericClosure.check thetaA thetaB rho piA piB N (value rows)

lemma check_sound {KA KB N : Nat} {thetaA thetaB rho : Rat}
    {piA : Fin KA → Rat} {piB : Fin KB → Rat}
    {rows : List (Config KA KB × Rat)}
    (h : check thetaA thetaB rho piA piB N rows = true) :
    ∃ (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho),
      (∀ ξ : Config KA KB, Rhone.Computation.CheckerSpec.InClosure N ξ →
        value rows ξ = q (πA := piA) (πB := piB) hA hB hR ξ) ∧
      ∀ row ∈ rows, row.2 = q (πA := piA) (πB := piB) hA hB hR row.1 := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrows, _⟩, ⟨_, hconflicts⟩⟩, hcheck⟩ := h
  obtain ⟨hA, hB, hR, hq⟩ := GenericClosure.check_sound hcheck
  refine ⟨hA, hB, hR, hq, ?_⟩
  intro row hr
  have hcl : Rhone.Computation.CheckerSpec.InClosure N row.1 := by
    simp only [List.all_eq_true, decide_eq_true_eq] at hrows
    exact hrows row hr
  rw [← noConflicts_sound hconflicts row hr]
  exact hq row.1 hcl

lemma present_true_iff {KA KB : Nat} (rows : List (Config KA KB × Rat)) (ξ : Config KA KB) :
    present rows ξ = true ↔ ∃ v, (ξ, v) ∈ rows := by
  simp only [present, List.any_eq_true]
  constructor
  · rintro ⟨row, hr, hs⟩
    have heq := (same_true_iff _ _).mp hs
    refine ⟨row.2, ?_⟩
    cases row with
    | mk η v =>
      change η = ξ at heq
      cases heq
      exact hr
  · rintro ⟨v, hr⟩
    exact ⟨(ξ, v), hr, (same_true_iff _ _).mpr rfl⟩

lemma check_complete {KA KB N : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho)
    (f : Config KA KB → Rat) (hf : IsSolution thetaA thetaB rho piA piB f) :
    check thetaA thetaB rho piA piB N
      ((keys KA KB N).map (fun ξ => (ξ, f ξ))) = true := by
  let rows := (keys KA KB N).map (fun ξ => (ξ, f ξ))
  have hv (ξ : Config KA KB) (hξ : CheckerSpec.InClosure N ξ) : value rows ξ = f ξ :=
    value_map _ _ _ ((mem_keys_iff ξ).mpr hξ)
  have hr : ∀ row ∈ rows, CheckerSpec.InClosure N row.1 := by
    intro row hrow
    obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.mp hrow
    exact (mem_keys_iff ξ).mp hξ
  simp only [check, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · simp only [List.all_eq_true, decide_eq_true_eq]
    exact hr
  · simp only [List.all_eq_true]
    intro ξ hξ
    apply (present_true_iff _ _).mpr
    exact ⟨f ξ, List.mem_map.mpr
      ⟨ξ, (mem_keys_iff ξ).mpr ((GenericClosure.mem_configs_iff ξ).mp hξ), rfl⟩⟩
  · simp only [uniqueKeys, List.map_map, Function.comp_def, decide_eq_true_eq]
    change ((keys KA KB N).map id).Nodup
    rw [List.map_id]
    exact List.nodup_dedup (GenericClosure.configs KA KB N)
  · simp only [noConflicts, List.all_eq_true, decide_eq_true_eq]
    intro row hrow
    obtain ⟨ξ, hξ, rfl⟩ := List.mem_map.mp hrow
    exact hv ξ ((mem_keys_iff ξ).mp hξ)
  · apply (GenericClosure.check_true_iff _ _ _ _ _ _ _).mpr
    refine ⟨⟨hA, hB, hR⟩, ?_⟩
    intro ξ hξ
    constructor
    · intro hn
      rw [hv ξ hξ]
      exact (GenericClosure.boundary_solution _ _ _ _ _ _ hf ξ hn).symm
    · intro hn
      rw [hv ξ hξ, hf.recursion ξ hn]
      apply rhs_congr
      intro η ha hb
      exact (hv η ⟨ha.trans hξ.1, hb.trans hξ.2⟩).symm

lemma check_input_integrity {KA KB N : Nat} {thetaA thetaB rho : Rat}
    {piA : Fin KA → Rat} {piB : Fin KB → Rat}
    {rows : List (Config KA KB × Rat)}
    (h : check thetaA thetaB rho piA piB N rows = true) :
    (rows.map Prod.fst).Nodup ∧
      (∀ row ∈ rows, CheckerSpec.InClosure N row.1) ∧
      (∀ ξ : Config KA KB, Rhone.Computation.CheckerSpec.InClosure N ξ → ∃ v, (ξ, v) ∈ rows) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrows, hcoverage⟩, ⟨hunique, _⟩⟩, _⟩ := h
  simp only [uniqueKeys, decide_eq_true_eq] at hunique
  simp only [List.all_eq_true, decide_eq_true_eq] at hrows
  simp only [List.all_eq_true] at hcoverage
  refine ⟨hunique, hrows, ?_⟩
  intro ξ hξ
  exact (present_true_iff _ _).mp
    (hcoverage ξ ((GenericClosure.mem_configs_iff ξ).mpr hξ))

end Rhone.Computation.GenericRows
