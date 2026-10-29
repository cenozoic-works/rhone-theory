/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWire
public import Std.Data.HashMap.Basic

/-! # General-allele closure and row checker with core-library definitions -/

@[expose] public section
namespace Rhone.Computation.GenericKernel
open Lean

def lsum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => lsum f k + f k

def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => nsum f k + f k

def countsL : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | d + 1, N => (List.range (N + 1)).flatMap fun a => (countsL d (N - a)).map (a :: ·)

def zero (ka kb : Nat) : Config :=
  ⟨Array.replicate ka 0, Array.replicate kb 0, Array.replicate (ka * kb) 0⟩

def configs (ka kb N : Nat) : List Config :=
  if N = 0 then [zero ka kb] else
  (countsL (ka * kb) N).flatMap fun c =>
    let budget := N - c.sum
    (countsL ka budget).flatMap fun a =>
      (countsL kb budget).map fun b => ⟨a.toArray, b.toArray, c.toArray⟩

def ca (x : Config) (i : Nat) : Nat := x.a.getD i 0

def cb (x : Config) (j : Nat) : Nat := x.b.getD j 0

def cc (kb : Nat) (x : Config) (i j : Nat) : Nat := x.c.getD (i * kb + j) 0

def tC (ka kb : Nat) (x : Config) : Nat := nsum (fun i => nsum (fun j => cc kb x i j) kb) ka

def nA (ka kb : Nat) (x : Config) : Nat := nsum (ca x) ka + tC ka kb x

def nB (ka kb : Nat) (x : Config) : Nat := nsum (cb x) kb + tC ka kb x

def nL (ka kb : Nat) (x : Config) : Nat := nsum (ca x) ka + nsum (cb x) kb + tC ka kb x

def dec (xs : Array Nat) (i : Nat) : Array Nat := xs.set! i (xs.getD i 0 - 1)

def inc (xs : Array Nat) (i : Nat) : Array Nat := xs.set! i (xs.getD i 0 + 1)

def dropA (x : Config) (i : Nat) : Config := ⟨dec x.a i, x.b, x.c⟩

def dropB (x : Config) (j : Nat) : Config := ⟨x.a, dec x.b j, x.c⟩

def dropC (kb : Nat) (x : Config) (i j : Nat) : Config := ⟨x.a, x.b, dec x.c (i * kb + j)⟩

def mergeAB (kb : Nat) (x : Config) (i j : Nat) : Config :=
  ⟨dec x.a i, dec x.b j, inc x.c (i * kb + j)⟩

def killA (kb : Nat) (x : Config) (i j : Nat) : Config :=
  ⟨x.a, inc x.b j, dec x.c (i * kb + j)⟩

def killB (kb : Nat) (x : Config) (i j : Nat) : Config :=
  ⟨inc x.a i, x.b, dec x.c (i * kb + j)⟩

def split (kb : Nat) (x : Config) (i j : Nat) : Config :=
  ⟨inc x.a i, inc x.b j, dec x.c (i * kb + j)⟩

def term (k : Nat) (v : Unit → Rat) : Rat := if k = 0 then 0 else (k : Rat) * v ()

def diag (p : Params) (x : Config) : Rat :=
  let ka := p.piA.size
  let kb := p.piB.size
  let n := nL ka kb x
  ((n * (n - 1) : Nat) : Rat) + p.thetaA * (nA ka kb x : Rat) + p.thetaB * (nB ka kb x : Rat) +
    p.rho * (tC ka kb x : Rat)

def boundary (p : Params) (x : Config) : Rat :=
  let ka := p.piA.size
  let kb := p.piB.size
  if nL ka kb x = 0 then 1 else
    lsum (fun i => (ca x i : Rat) * p.piA.getD i 0) ka +
      lsum (fun j => (cb x j : Rat) * p.piB.getD j 0) kb +
      lsum (fun i => lsum (fun j => (cc kb x i j : Rat) * p.piA.getD i 0 * p.piB.getD j 0) kb) ka

def rhs (p : Params) (value : Config → Rat) (x : Config) : Rat :=
  let ka := p.piA.size
  let kb := p.piB.size
  let rowSum := fun i => nsum (fun j => cc kb x i j) kb
  let colSum := fun j => nsum (fun i => cc kb x i j) ka
  lsum (fun i => term (ca x i * (ca x i - 1 + 2 * rowSum i)) fun _ => value (dropA x i)) ka
    + lsum (fun j => term (cb x j * (cb x j - 1 + 2 * colSum j)) fun _ => value (dropB x j)) kb
    + lsum (fun i => lsum (fun j =>
        term (cc kb x i j * (cc kb x i j - 1)) fun _ => value (dropC kb x i j)) kb) ka
    + lsum (fun i => lsum (fun j =>
        term (2 * (ca x i * cb x j)) fun _ => value (mergeAB kb x i j)) kb) ka
    + p.thetaA * lsum (fun i => p.piA.getD i 0 * (term (ca x i) (fun _ => value (dropA x i))
        + lsum (fun j => term (cc kb x i j) fun _ => value (killA kb x i j)) kb)) ka
    + p.thetaB * lsum (fun j => p.piB.getD j 0 * (term (cb x j) (fun _ => value (dropB x j))
        + lsum (fun i => term (cc kb x i j) fun _ => value (killB kb x i j)) ka)) kb
    + p.rho * lsum (fun i => lsum (fun j =>
        term (cc kb x i j) fun _ => value (split kb x i j)) kb) ka

def closureCheck (p : Params) (N : Nat) (value : Config → Rat) : Bool :=
  decide (0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho) &&
    (configs p.piA.size p.piB.size N).all (fun x =>
      if nL p.piA.size p.piB.size x ≤ 1 then decide (value x = boundary p x)
      else decide (diag p x * value x = rhs p value x))

abbrev Key := Array Nat × Array Nat × Array Nat

def keyOf (x : Config) : Key := (x.a, x.b, x.c)

def insertRows : List (Config × Rat) → Std.HashMap Key Rat → Option (Std.HashMap Key Rat)
  | [], m => some m
  | row :: rows, m =>
    if m.contains (keyOf row.1) then none else insertRows rows (m.insert (keyOf row.1) row.2)

def inClosure (ka kb N : Nat) (x : Config) : Bool := nA ka kb x ≤ N && nB ka kb x ≤ N

def rowsCheck (p : Params) (N : Nat) (rows : List (Config × Rat)) : Bool :=
  rows.all (fun row => inClosure p.piA.size p.piB.size N row.1) &&
    match insertRows rows {} with
    | none => false
    | some table =>
      (configs p.piA.size p.piB.size N).all (fun x => table.contains (keyOf x)) &&
        closureCheck p N (fun x => table.getD (keyOf x) 0)

def asum (xs : Array Rat) : Rat := lsum (fun i => xs.getD i 0) xs.size

def valid (p : Params) : Bool :=
  decide (0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho) &&
    (0 < p.piA.size && p.piA.size ≤ 255 && 0 < p.piB.size && p.piB.size ≤ 255) &&
    ((List.range p.piA.size).all fun i => decide (0 < p.piA.getD i 0)) &&
    ((List.range p.piB.size).all fun j => decide (0 < p.piB.getD j 0)) &&
    decide (asum p.piA = 1) && decide (asum p.piB = 1)

structure Request where
  params : Params
  bound : Nat
  rawRows : Array (Config × Rat)

def Request.accepted (r : Request) : Bool :=
  (valid r.params && r.rawRows.all (fun row =>
    row.1.a.size == r.params.piA.size && row.1.b.size == r.params.piB.size &&
      row.1.c.size == r.params.piA.size * r.params.piB.size)) &&
    rowsCheck r.params r.bound r.rawRows.toList

def fieldsAllowed (doc : Json) (allowed : List String) : Except String Unit := do
  let fields ← doc.getObj?
  if fields.toList.all (fun field => allowed.contains field.1) then return ()
  else throw "unsupported general-table field"

def entry (ka kb : Nat) (doc : Json) : Except String (Config × Rat) := do
  fieldsAllowed doc ["key", "value"]
  let key ← doc.getObjValAs? String "key"
  let value ← doc.getObjValAs? String "value" >>= RationalWire.decode
  let config ← parseConfig key ka kb
  return (config, value)

def decode (doc : Json) : Except String Request := do
  fieldsAllowed doc ["op", "n", "theta_a", "theta_b", "rho", "pi_a", "pi_b",
    "entries", "rhone_version", "provenance"]
  let operation ← doc.getObjValAs? String "op"
  if operation != "check_table_general" then throw "unsupported operation"
  let bound ← doc.getObjValAs? Nat "n"
  if bound > 65535 then throw "unsupported bound: exceeds the u16 configuration wire domain"
  let params ← ParamsWire.decode doc
  if !valid params then throw "invalid parameter domain"
  let rows ← (doc.getObjVal? "entries" >>= Json.getArr?) >>= fun rows =>
    rows.mapM (entry params.piA.size params.piB.size)
  return ⟨params, bound, rows⟩

def checkRequest (doc : Json) : Except String Bool := do
  let r ← decode doc
  return r.accepted

def request (line : String) : Except String Bool := Json.parse line >>= checkRequest

end Rhone.Computation.GenericKernel
