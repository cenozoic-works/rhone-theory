/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.QWire

/-! # Unordered two-locus sampling probability with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.QUnordered
open Lean

def factorial (n : Nat) : Nat := (List.range n).foldl (fun acc k => acc * (k + 1)) 1

def fullyTyped (c : Config) : Bool := c.a.all (· == 0) && c.b.all (· == 0)

def factor (c : Config) : Nat :=
  factorial (c.c.foldl (· + ·) 0) / c.c.foldl (fun acc k => acc * factorial k) 1

def decode (doc : Json) : Except String QWire.Request := do
  let operation ← (doc.getObjVal? "op").bind Json.getStr?
  let key ← (doc.getObjVal? "key").bind Json.getStr?
  if operation != "q_unordered" then throw "unsupported operation"
  let config ← parseConfig key
  let params ← ParamsWire.decode doc
  return ⟨params, config⟩

def evaluate (r : QWire.Request) : Except String Rat := do
  if !fullyTyped r.config then throw "unordered probability needs a fully typed sample"
  let value ← q r.params r.config
  return (factor r.config : Rat) * value

def result (value : Rat) : Json :=
  Json.mkObj [("p", .str (RationalWire.strictPrint value))]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  let value ← evaluate r
  return result value

def request (line : String) : Except String Json := Json.parse line >>= requestAst

end Rhone.Computation.QUnordered
