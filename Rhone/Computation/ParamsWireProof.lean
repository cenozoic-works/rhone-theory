/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWire
public import Rhone.Computation.RationalWirePrintProof
public import Rhone.Computation.ParamsProof
import all Lean.Data.Json.Basic
public import Std.Data.TreeMap.Raw.Lemmas
public import Init.Data.Array.Monadic

/-! # Parameter AST roundtrip and unchanged domain -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

theorem encode_getObjVal {p : Params} {name : String} {value : Json}
    (hmem : (name, value) ∈ fields p) :
    (encode p).getObjVal? name = .ok value := by
  have hdistinct : (fields p).Pairwise
      (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simp [fields]
  have hlookup := Std.TreeMap.Raw.getElem?_ofList_of_mem
    (cmp := compare) (k' := name) (by simp) hdistinct hmem
  change (Std.TreeMap.Raw.ofList (fields p) compare).get? name = some value at hlookup
  change (match (Std.TreeMap.Raw.ofList (fields p) compare).get? name with
    | some v => Except.ok v
    | none => Except.error s!"property not found: {name}") = Except.ok value
  rw [hlookup]

theorem rational_strictPrint (r : Rat) :
    rational (.str (RationalWire.strictPrint r)) = .ok r := by
  simpa [rational, Json.getStr?] using
    RationalWire.decode_strictPrint r

theorem frequencies_strictPrint (xs : Array Rat) :
    frequencies (.arr (xs.map fun r => .str (RationalWire.strictPrint r))) =
      .ok xs := by
  simp only [frequencies, Json.getArr?, pure_bind, Array.mapM_map]
  have hfun : (rational ∘ fun r => Json.str (RationalWire.strictPrint r)) =
      fun r => (pure r : Except String Rat) := by
    funext r
    exact rational_strictPrint r
  rw [hfun, Array.mapM_pure]
  change (pure (xs.map id) : Except String (Array Rat)) = .ok xs
  rw [Array.map_id]
  rfl

theorem decode_encode (p : Params) : decode (encode p) = .ok p := by
  have hθA := encode_getObjVal (p := p) (by simp [fields] :
    ("theta_a", Json.str (RationalWire.strictPrint p.thetaA)) ∈ fields p)
  have hθB := encode_getObjVal (p := p) (by simp [fields] :
    ("theta_b", Json.str (RationalWire.strictPrint p.thetaB)) ∈ fields p)
  have hρ := encode_getObjVal (p := p) (by simp [fields] :
    ("rho", Json.str (RationalWire.strictPrint p.rho)) ∈ fields p)
  have hπA := encode_getObjVal (p := p) (by simp [fields] :
    ("pi_a", Json.arr (p.piA.map fun r => Json.str (RationalWire.strictPrint r))) ∈ fields p)
  have hπB := encode_getObjVal (p := p) (by simp [fields] :
    ("pi_b", Json.arr (p.piB.map fun r => Json.str (RationalWire.strictPrint r))) ∈ fields p)
  have ha : rationalField (encode p) "theta_a" = .ok p.thetaA := by
    rw [rationalField, hθA]
    exact rational_strictPrint p.thetaA
  have hb : rationalField (encode p) "theta_b" = .ok p.thetaB := by
    rw [rationalField, hθB]
    exact rational_strictPrint p.thetaB
  have hr : rationalField (encode p) "rho" = .ok p.rho := by
    rw [rationalField, hρ]
    exact rational_strictPrint p.rho
  have hpa : frequencyField (encode p) "pi_a" = .ok p.piA := by
    rw [frequencyField, hπA]
    exact frequencies_strictPrint p.piA
  have hpb : frequencyField (encode p) "pi_b" = .ok p.piB := by
    rw [frequencyField, hπB]
    exact frequencies_strictPrint p.piB
  simp only [decode, ha, hb, hr, hpa, hpb]
  rfl

theorem encoded_domain_iff (p : Params) :
    (decode (encode p)).map Params.valid = .ok true ↔
      0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho ∧
      p.piA.size = 2 ∧ p.piB.size = 2 ∧
      (∀ i : Fin 2, 0 < p.piA.getD i.val 0) ∧
      (∀ i : Fin 2, 0 < p.piB.getD i.val 0) ∧
      (∑ i : Fin 2, p.piA.getD i.val 0) = 1 ∧
      (∑ i : Fin 2, p.piB.getD i.val 0) = 1 := by
  rw [decode_encode]
  simpa only [Except.map, Except.ok.injEq] using Params.valid_iff p

end Rhone.Computation.ParamsWire
