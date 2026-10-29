/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init

/-! # Executable sample configurations -/

@[expose] public section

namespace Rhone.Computation

structure Config where
  a : Array Nat
  b : Array Nat
  c : Array Nat
  deriving BEq, Inhabited

def Config.block (c : Config) : Nat × Nat :=
  let t := c.c.foldl (· + ·) 0
  (c.a.foldl (· + ·) t, c.b.foldl (· + ·) t)

def formatCounts (xs : Array Nat) : String :=
  "(" ++ String.intercalate "," (xs.toList.map toString) ++ ")"

def Config.key (c : Config) : String :=
  let rows := (List.range c.a.size).map fun i =>
    formatCounts ((List.range c.b.size).toArray.map fun j => c.c.getD (i*c.b.size+j) 0)
  s!"a={formatCounts c.a};b={formatCounts c.b};c=({String.intercalate "," rows})"

def expect (s : Array Char) (pos : Nat) (lit : String) : Except String Nat := do
  let mut p := pos
  for ch in lit.toList do
    if s[p]? != some ch then throw s!"expected {lit} at character {p}"
    p := p + 1
  return p

def count (s : Array Char) (pos : Nat) : Except String (Nat × Nat) := do
  let mut p := pos
  let mut n := 0
  for _ in [pos:s.size] do
    let ch := s.getD p '\x00'
    if !ch.isDigit then break
    n := 10*n + (ch.toNat - '0'.toNat)
    if n > 65535 then throw "count exceeds u16"
    p := p + 1
  if p == pos then throw "expected decimal count"
  if p > pos+1 && s[pos]? == some '0' then throw "leading zero"
  return (n, p)

def counts (s : Array Char) (pos n : Nat) : Except String (Array Nat × Nat) := do
  let mut p := pos
  let mut out := #[]
  for k in [0:n] do
    if k > 0 then p ← expect s p ","
    let (v, next) ← count s p
    out := out.push v
    p := next
  return (out, p)

def decimalCount (digits : List Char) : Nat :=
  digits.foldl (fun n ch => min 65536 (10*n + (ch.toNat - '0'.toNat))) 0

def keyCounts (input : String) : List Nat :=
  (input.toList.splitOnP fun ch => !ch.isDigit).filterMap fun digits =>
    if digits = [] then none else some (decimalCount digits)

def parseConfigRaw (input : String) (ka kb : Nat := 2) : Except String Config := do
  if ka == 0 || kb == 0 || ka > 255 || kb > 255 then throw "invalid shape"
  let values := keyCounts input
  if values.any (· > 65535) then throw "count exceeds u16"
  if values.length != ka + kb + ka*kb then throw "wrong count vector lengths"
  return ⟨(values.take ka).toArray, ((values.drop ka).take kb).toArray,
    (values.drop (ka+kb)).toArray⟩

def parseConfig (input : String) (ka kb : Nat := 2) : Except String Config :=
  match parseConfigRaw input ka kb with
  | .error e => .error e
  | .ok c => if c.key = input then .ok c else .error "noncanonical configuration key"

end Rhone.Computation
