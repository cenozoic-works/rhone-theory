/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWireTyped
public import Rhone.Computation.ParamsWireAcceptanceProof
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic
import all Init.Control.Except

/-! # Typed parameter decoding agrees with the checked parameter codec -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl

@[simp] private theorem pure_def {α : Type} (a : α) :
    (pure a : Except String α) = Except.ok a := rfl

private theorem bind_eq_ok_iff {α β : Type} (x : Except String α)
    (f : α → Except String β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  change Except.bind x f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y
  cases x <;> simp [Except.bind]

private theorem pure_eq_ok_iff {α : Type} (a b : α) :
    (pure a : Except String α) = .ok b ↔ a = b := by
  change Except.ok a = Except.ok b ↔ a = b
  simp only [Except.ok.injEq]

theorem typedRationalField_eq_ok_iff (doc : Json) (name : String) (r : Rat) :
    typedRationalField doc name = .ok r ↔ rationalField doc name = .ok r := by
  change (Json.getStr? ((doc.getObjVal? name).toOption.getD .null) >>=
    RationalWire.decode) = .ok r ↔ _
  cases h : doc.getObjVal? name with
  | error e =>
    simp [h, rationalField, rational, Json.getStr?, Except.toOption, Option.getD,
      bind_eq_ok_iff]
  | ok value =>
    cases value <;>
      simp [h, rationalField, rational, Json.getStr?, Except.toOption, Option.getD, bind_eq_ok_iff]

private theorem decodeTyped_eq_fields_iff (doc : Json) (p : Params) :
    decodeTyped doc = .ok p ↔
      typedRationalField doc "theta_a" = .ok p.thetaA ∧
      typedRationalField doc "theta_b" = .ok p.thetaB ∧
      typedRationalField doc "rho" = .ok p.rho ∧
      frequencyField doc "pi_a" = .ok p.piA ∧
      frequencyField doc "pi_b" = .ok p.piB := by
  rcases p with ⟨thetaA, thetaB, rho, piA, piB⟩
  simp only [decodeTyped, bind_eq_ok_iff, pure_eq_ok_iff, Params.mk.injEq]
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

theorem decodeTyped_eq_ok_iff (doc : Json) (p : Params) :
    decodeTyped doc = .ok p ↔ decode doc = .ok p := by
  rw [decodeTyped_eq_fields_iff, decode_eq_ok_iff]
  simp only [typedRationalField_eq_ok_iff]

theorem decodeTyped_encode (p : Params) : decodeTyped (encode p) = .ok p :=
  (decodeTyped_eq_ok_iff _ _).mpr (decode_encode p)

theorem decodeTyped_congr {a b : Json}
    (hθA : a.getObjVal? "theta_a" = b.getObjVal? "theta_a")
    (hθB : a.getObjVal? "theta_b" = b.getObjVal? "theta_b")
    (hρ : a.getObjVal? "rho" = b.getObjVal? "rho")
    (hπA : a.getObjVal? "pi_a" = b.getObjVal? "pi_a")
    (hπB : a.getObjVal? "pi_b" = b.getObjVal? "pi_b") :
    decodeTyped a = decodeTyped b := by
  simp only [decodeTyped, typedRationalField, Json.getObjValAs?, Json.getObjValD,
    frequencyField, hθA, hθB, hρ, hπA, hπB]

end Rhone.Computation.ParamsWire
