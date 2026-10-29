/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWireProof
import all Lean.Data.Json.Basic

/-! # Exact parameter AST acceptance -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

private theorem bind_eq_ok_iff {α β : Type} (x : Except String α)
    (f : α → Except String β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  change Except.bind x f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y
  cases x <;> simp [Except.bind]

private theorem pure_eq_ok_iff {α : Type} (a b : α) :
    (pure a : Except String α) = .ok b ↔ a = b := by
  change Except.ok a = Except.ok b ↔ a = b
  simp only [Except.ok.injEq]

private theorem list_mapM_success_iff {α β : Type} (f : α → Except String β)
    (xs : List α) :
    (∃ ys, xs.mapM f = .ok ys) ↔ ∀ x ∈ xs, ∃ y, f x = .ok y := by
  induction xs with
  | nil => simp [pure_eq_ok_iff]
  | cons x xs ih =>
    cases hx : f x <;> cases hxs : xs.mapM f <;>
      simp_all [List.mapM_cons, bind_eq_ok_iff]

private theorem array_mapM_success_iff {α β : Type} (f : α → Except String β)
    (xs : Array α) :
    (∃ ys, xs.mapM f = .ok ys) ↔ ∀ x ∈ xs, ∃ y, f x = .ok y := by
  have h := list_mapM_success_iff f xs.toList
  rw [Array.mapM_eq_mapM_toList]
  change (∃ ys, Except.map List.toArray (xs.toList.mapM f) = .ok ys) ↔ _
  cases hresult : xs.toList.mapM f <;>
    simpa [hresult, Except.map] using h

theorem rational_eq_ok_iff (value : Json) (r : Rat) :
    rational value = .ok r ↔
      ∃ s, value = .str s ∧ RationalWire.decode s = .ok r := by
  cases value <;> simp [rational, Json.getStr?, bind_eq_ok_iff]

theorem rational_success_iff (value : Json) :
    (∃ r, rational value = .ok r) ↔
      ∃ s r, value = .str s ∧ RationalWire.decode s = .ok r := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs, hd⟩ := (rational_eq_ok_iff value r).mp hr
    exact ⟨s, r, hs, hd⟩
  · rintro ⟨s, r, hs, hd⟩
    exact ⟨r, (rational_eq_ok_iff value r).mpr ⟨s, hs, hd⟩⟩

theorem frequencies_success_iff (value : Json) :
    (∃ rs, frequencies value = .ok rs) ↔
      ∃ xs : Array Json, value = .arr xs ∧
        ∀ v ∈ xs, ∃ s r, v = .str s ∧ RationalWire.decode s = .ok r := by
  cases value <;>
    simp [frequencies, Json.getArr?, bind_eq_ok_iff, array_mapM_success_iff,
      rational_success_iff]

def HasRationalField (doc : Json) (name : String) : Prop :=
  ∃ s, doc.getObjVal? name = .ok (.str s) ∧
    ∃ r, RationalWire.decode s = .ok r

def HasFrequencyField (doc : Json) (name : String) : Prop :=
  ∃ xs : Array Json, doc.getObjVal? name = .ok (.arr xs) ∧
    ∀ v ∈ xs, ∃ s r, v = .str s ∧ RationalWire.decode s = .ok r

private theorem rationalField_success_iff (doc : Json) (name : String) :
    (∃ r, rationalField doc name = .ok r) ↔ HasRationalField doc name := by
  constructor
  · rintro ⟨r, h⟩
    obtain ⟨v, hv, hr⟩ := (bind_eq_ok_iff _ _ _).mp h
    obtain ⟨s, rfl, hs⟩ := (rational_eq_ok_iff v r).mp hr
    exact ⟨s, hv, r, hs⟩
  · rintro ⟨s, hs, r, hr⟩
    exact ⟨r, (bind_eq_ok_iff _ _ _).mpr
      ⟨.str s, hs, (rational_eq_ok_iff _ _).mpr ⟨s, rfl, hr⟩⟩⟩

private theorem frequencyField_success_iff (doc : Json) (name : String) :
    (∃ rs, frequencyField doc name = .ok rs) ↔ HasFrequencyField doc name := by
  constructor
  · rintro ⟨rs, h⟩
    obtain ⟨v, hv, hr⟩ := (bind_eq_ok_iff _ _ _).mp h
    obtain ⟨xs, rfl, hx⟩ := (frequencies_success_iff v).mp ⟨rs, hr⟩
    exact ⟨xs, hv, hx⟩
  · rintro ⟨xs, hx, hall⟩
    obtain ⟨rs, hr⟩ := (frequencies_success_iff (.arr xs)).mpr ⟨xs, rfl, hall⟩
    exact ⟨rs, (bind_eq_ok_iff _ _ _).mpr ⟨.arr xs, hx, hr⟩⟩

theorem decode_eq_ok_iff (doc : Json) (p : Params) :
    decode doc = .ok p ↔
      rationalField doc "theta_a" = .ok p.thetaA ∧
      rationalField doc "theta_b" = .ok p.thetaB ∧
      rationalField doc "rho" = .ok p.rho ∧
      frequencyField doc "pi_a" = .ok p.piA ∧
      frequencyField doc "pi_b" = .ok p.piB := by
  rcases p with ⟨thetaA, thetaB, rho, piA, piB⟩
  simp only [decode, bind_eq_ok_iff, pure_eq_ok_iff, Params.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, r, hr, pa, hpa, pb, hpb, hθA, hθB, hρ, hπA, hπB⟩
    subst a
    subst b
    subst r
    subst pa
    subst pb
    exact ⟨ha, hb, hr, hpa, hpb⟩
  · rintro ⟨ha, hb, hr, hpa, hpb⟩
    exact ⟨thetaA, ha, thetaB, hb, rho, hr, piA, hpa, piB, hpb,
      rfl, rfl, rfl, rfl, rfl⟩

theorem decode_success_iff (doc : Json) :
    (∃ p, decode doc = .ok p) ↔
      HasRationalField doc "theta_a" ∧ HasRationalField doc "theta_b" ∧
      HasRationalField doc "rho" ∧ HasFrequencyField doc "pi_a" ∧
      HasFrequencyField doc "pi_b" := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨ha, hb, hr, hpa, hpb⟩ := (decode_eq_ok_iff doc p).mp hp
    exact ⟨(rationalField_success_iff _ _).mp ⟨_, ha⟩,
      (rationalField_success_iff _ _).mp ⟨_, hb⟩,
      (rationalField_success_iff _ _).mp ⟨_, hr⟩,
      (frequencyField_success_iff _ _).mp ⟨_, hpa⟩,
      (frequencyField_success_iff _ _).mp ⟨_, hpb⟩⟩
  · rintro ⟨ha, hb, hr, hpa, hpb⟩
    obtain ⟨a, ha⟩ := (rationalField_success_iff _ _).mpr ha
    obtain ⟨b, hb⟩ := (rationalField_success_iff _ _).mpr hb
    obtain ⟨r, hr⟩ := (rationalField_success_iff _ _).mpr hr
    obtain ⟨pa, hpa⟩ := (frequencyField_success_iff _ _).mpr hpa
    obtain ⟨pb, hpb⟩ := (frequencyField_success_iff _ _).mpr hpb
    exact ⟨⟨a, b, r, pa, pb⟩, (decode_eq_ok_iff _ _).mpr ⟨ha, hb, hr, hpa, hpb⟩⟩

theorem decode_congr {a b : Json}
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b") : decode a = decode b := by
  simp only [decode, rationalField, frequencyField, hθA, hθB, hρ, hπA, hπB]

end Rhone.Computation.ParamsWire
