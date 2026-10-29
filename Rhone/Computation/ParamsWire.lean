/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Rhone.Computation.RationalWire
public import Lean.Data.Json

/-! # Exact parameter JSON AST codec -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

def rational (value : Json) : Except String Rat :=
  value.getStr? >>= RationalWire.decode

def frequencies (value : Json) : Except String (Array Rat) := do
  let values ← value.getArr?
  values.mapM rational

def rationalField (doc : Json) (name : String) : Except String Rat :=
  doc.getObjVal? name >>= rational

def frequencyField (doc : Json) (name : String) : Except String (Array Rat) :=
  doc.getObjVal? name >>= frequencies

def decode (doc : Json) : Except String Params := do
  let thetaA ← rationalField doc "theta_a"
  let thetaB ← rationalField doc "theta_b"
  let rho ← rationalField doc "rho"
  let piA ← frequencyField doc "pi_a"
  let piB ← frequencyField doc "pi_b"
  return ⟨thetaA, thetaB, rho, piA, piB⟩

def fields (p : Params) : List (String × Json) :=
  [("theta_a", .str (RationalWire.strictPrint p.thetaA)),
   ("theta_b", .str (RationalWire.strictPrint p.thetaB)),
   ("rho", .str (RationalWire.strictPrint p.rho)),
   ("pi_a", .arr (p.piA.map fun r => .str (RationalWire.strictPrint r))),
   ("pi_b", .arr (p.piB.map fun r => .str (RationalWire.strictPrint r)))]

def encode (p : Params) : Json := Json.mkObj (fields p)

end Rhone.Computation.ParamsWire
