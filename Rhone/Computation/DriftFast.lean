/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftFull

/-! # Fraction-free evaluation of the full drift comparison -/

@[expose] public section
namespace Rhone.Computation.DriftFast
open Lean

def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => isum f k + f k

def denLcm (n : Nat) (f : Nat → Nat → Rat) : Nat :=
  (List.range (n + 1)).foldl
    (fun acc k => (List.range (n + 1)).foldl (fun acc j => Nat.lcm acc (f k j).den) acc) 1

def denLcmVec (n : Nat) (g : Nat → Rat) : Nat :=
  (List.range (n + 1)).foldl (fun acc j => Nat.lcm acc (g j).den) 1

def scaledMatrix (n : Nat) (row : Nat → Nat → Rat) (D : Nat) : Array (Array Int) :=
  ((List.range (n + 1)).map fun k =>
    ((List.range (n + 1)).map fun j => (row k j * D).num).toArray).toArray

def scaleOk (n : Nat) (row : Nat → Nat → Rat) (D : Nat) : Bool :=
  D != 0 && (List.range (n + 1)).all fun k =>
    (List.range (n + 1)).all fun j => (row k j * D).den == 1

def scaleVecOk (n : Nat) (g : Nat → Rat) (G : Nat) : Bool :=
  G != 0 && (List.range (n + 1)).all fun j => (g j * G).den == 1

def entry (M : Array (Array Int)) (k j : Nat) : Int := (M.getD k #[]).getD j 0

def pointVec (n i : Nat) : Array Int :=
  ((List.range (n + 1)).map fun j => if j = i then (1 : Int) else 0).toArray

def stepVec (n : Nat) (M : Array (Array Int)) (v : Array Int) : Array Int :=
  ((List.range (n + 1)).map fun j => isum (fun k => v.getD k 0 * entry M k j) (n + 1)).toArray

def vecAfter (n : Nat) (M : Array (Array Int)) (i : Nat) : Nat → Array Int
  | 0 => pointVec n i
  | t + 1 => stepVec n M (vecAfter n M i t)

def lawMatches (n : Nat) (claim : Array Rat) (v : Array Int) (E : Nat) : Bool :=
  claim.size == n + 1 && (List.range (n + 1)).all fun j =>
    (claim.getD j 0).num * E == v.getD j 0 * (claim.getD j 0).den

def scalarMatches (h : Rat) (X : Int) (E : Nat) : Bool :=
  h.num * E == X * h.den

def lawCheck (n : Nat) (row : Nat → Nat → Rat) (i t : Nat) (distribution : Array Rat)
    (heterozygosity : Rat) : Bool :=
  let D := denLcm n row
  let G := denLcmVec n (Drift.heterozygosity n)
  if scaleOk n row D && scaleVecOk n (Drift.heterozygosity n) G then
    let M := scaledMatrix n row D
    let v := vecAfter n M i t
    let E := D ^ t
    let X := isum (fun j => v.getD j 0 * (Drift.heterozygosity n j * G).num) (n + 1)
    lawMatches n distribution v E && scalarMatches heterozygosity X (E * G)
  else
    let law := Drift.lawAfter n row i t
    decide (distribution = law) &&
      decide (heterozygosity = Drift.lawHeterozygosity n law)

def Request.kernel (r : DriftFull.Request) : Array (Array Rat) :=
  if r.base.moran then Absorption.moranKernel r.base.geneCopies r.base.fitness
  else Absorption.wfKernel r.base.geneCopies

def Request.row (r : DriftFull.Request) : Nat → Nat → Rat :=
  Drift.kernelEntry (Request.kernel r)

def Request.checkFast (r : DriftFull.Request) : Bool :=
  let kernel := Request.kernel r
  r.base.check &&
    lawCheck r.base.geneCopies (Drift.kernelEntry kernel) r.base.initialCount r.base.steps
      r.distribution r.heterozygosity &&
    r.tableCheck && decide (r.absorption = r.table.getD r.base.initialCount 0)

def decision (doc : Json) : Except String (Bool × Nat) :=
  match DriftFull.decode doc with
  | .error message => .error message
  | .ok r =>
    if r.base.valid then .ok (Request.checkFast r, r.count)
    else .error "unsupported drift request domain"

def requestAst (doc : Json) : Except String Json := (decision doc).map DriftFull.stamp

def request (line : String) : Except String Json :=
  Json.parse line >>= requestAst

end Rhone.Computation.DriftFast
