/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Hierarchy
public import Rhone.Computation.ParamsWire

/-! # Production q request sequence on JSON abstract syntax trees -/

@[expose] public section
namespace Rhone.Computation.QWire
open Lean

structure Request where
  params : Params
  config : Config

def decode (doc : Json) : Except String Request := do
  let operation ← (doc.getObjVal? "op").bind Json.getStr?
  let key ← (doc.getObjVal? "key").bind Json.getStr?
  if operation != "q" then throw "unsupported operation"
  let config ← parseConfig key
  let params ← ParamsWire.decode doc
  return ⟨params, config⟩

def Request.evaluate (r : Request) : Except String Rat := q r.params r.config

def result (value : Rat) : Json :=
  Json.mkObj [("q", .str (RationalWire.strictPrint value))]

def requestAst (doc : Json) : Except String Json := do
  let r ← decode doc
  let value ← r.evaluate
  return result value

def request (line : String) : Except String Json := Json.parse line >>= requestAst

def requestFields (r : Request) : List (String × Json) :=
  [("op", .str "q"), ("key", .str r.config.key)] ++ ParamsWire.fields r.params

def encode (r : Request) : Json := Json.mkObj (requestFields r)

end Rhone.Computation.QWire
