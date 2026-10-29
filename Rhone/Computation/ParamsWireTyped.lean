/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWire

/-! # Existing checker typed-getter parameter sequence -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

def typedRationalField (doc : Json) (name : String) : Except String Rat :=
  doc.getObjValAs? String name >>= RationalWire.decode

def decodeTyped (doc : Json) : Except String Params := do
  let thetaA ← typedRationalField doc "theta_a"
  let thetaB ← typedRationalField doc "theta_b"
  let rho ← typedRationalField doc "rho"
  let piA ← frequencyField doc "pi_a"
  let piB ← frequencyField doc "pi_b"
  return ⟨thetaA, thetaB, rho, piA, piB⟩

end Rhone.Computation.ParamsWire
