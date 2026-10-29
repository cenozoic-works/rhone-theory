/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Config
public import Init.Data.Rat
public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.AdditionalOperations

/-! # Compiled biallelic hierarchy -/

@[expose] public section

namespace Rhone.Computation

structure Params where
  thetaA : Rat
  thetaB : Rat
  rho : Rat
  piA : Array Rat
  piB : Array Rat
  deriving Inhabited

def Params.valid (p : Params) : Bool :=
  p.thetaA > 0 && p.thetaB > 0 && p.rho ≥ 0 &&
  p.piA.size == 2 && p.piB.size == 2 &&
  p.piA.all (· > 0) && p.piB.all (· > 0) &&
  p.piA.foldl (· + ·) 0 == 1 && p.piB.foldl (· + ·) 0 == 1

structure PhiTable where
  nb : Nat
  blocks : Array (Array Rat)
  deriving Inhabited

def PhiTable.get (tab : PhiTable) (i j t : Nat) : Rat :=
  if t > min i j then 0 else (tab.blocks.getD (i*(tab.nb+1)+j) #[]).getD t 0

def source (p : Params) (tab : PhiTable) (i j t : Nat) : Rat := Id.run do
  let ka := p.piA.getD 0 0 * p.piA.getD 1 0
  let kb := p.piB.getD 0 0 * p.piB.getD 1 0
  let ga := p.piA.getD 1 0 - p.piA.getD 0 0
  let gb := p.piB.getD 1 0 - p.piB.getD 0 0
  let terms := #[
    ((i-t)*(i-t-1), ka, i-2, j, t),
    (2*(i-t)*t, ka, i-2, j, t-1),
    ((i-t)*(i+t-1), ga, i-1, j, t),
    ((j-t)*(j-t-1), kb, i, j-2, t),
    (2*(j-t)*t, kb, i, j-2, t-1),
    ((j-t)*(j+t-1), gb, i, j-1, t),
    (t*(t-1), ka*kb, i-2, j-2, t-2),
    (t*(t-1), ka*gb, i-2, j-1, t-2),
    (t*(t-1), ga*kb, i-1, j-2, t-2),
    (t*(t-1), ga*gb, i-1, j-1, t-1)]
  let mut acc : Rat := 0
  for (coef, scale, bi, bj, bt) in terms do
    if coef > 0 then acc := acc + (coef : Rat)*scale*tab.get bi bj bt
  return acc

def rangeProduct (lo hi : Nat) : Nat := Id.run do
  let mut acc := 1
  for u in [lo+1:hi+1] do acc := acc*u
  return acc

def blockDiagonal (p : Params) (i j s : Nat) : Rat :=
  let n := i + j - s
  (n * (n - 1) : Rat) + (i : Rat) * p.thetaA + (j : Rat) * p.thetaB + (s : Rat) * p.rho

def blockBeta (p : Params) (i j s : Nat) : Rat :=
  (2 * s * (i + 1 - s) * (j + 1 - s) : Rat) * p.rho

def forwardContinuants (diag beta : Nat → Rat) (steps : Nat) : Array Rat := Id.run do
  let mut ps : Array Rat := #[0, 1]
  for s in [0:steps] do
    ps := ps.push (diag s * ps.getD (s+1) 0 - beta s * ps.getD s 0)
  return ps

def backwardContinuants (diag beta : Nat → Rat) (m : Nat) : Array Rat := Id.run do
  let mut qs : Array Rat := (Array.replicate (m+3) 0).set! (m+1) 1
  for k in [0:m+1] do
    let s := m-k
    qs := qs.set! s (diag s * qs.getD (s+1) 0 - beta (s+1) * qs.getD (s+2) 0)
  return qs

def blockInverseEntry (p : Params) (i j : Nat) (ps qs : Array Rat) (invDet : Rat)
    (t u : Nat) : Rat :=
  if t ≤ u then
    ((2^(u-t) * rangeProduct (i-u) (i-t) * rangeProduct (j-u) (j-t) : Nat) : Rat) *
      ps.getD (t+1) 0 * qs.getD (u+1) 0 * invDet
  else
    p.rho^(t-u) * (rangeProduct u t : Rat) *
      ps.getD (u+1) 0 * qs.getD (t+1) 0 * invDet

def applyBlockInverse (p : Params) (i j : Nat) (ps qs : Array Rat) (invDet : Rat)
    (rhs : Array Rat) : Array Rat := Id.run do
  let m := min i j
  let mut out := #[]
  for t in [0:m+1] do
    let mut acc : Rat := 0
    for u in [0:m+1] do
      let v := blockInverseEntry p i j ps qs invDet t u
      acc := acc + v * rhs.getD u 0
    out := out.push acc
  return out

def solveBlock (p : Params) (i j : Nat) (rhs : Array Rat) :
    Except String (Array Rat) := do
  let m := min i j
  let diag := blockDiagonal p i j
  let beta := blockBeta p i j
  let ps := forwardContinuants diag beta (m+1)
  let qs := backwardContinuants diag beta m
  let det := ps.getD (m+2) 0
  if det == 0 then throw s!"zero determinant at ({i},{j})"
  if det != qs.getD 0 0 then throw s!"continuants disagree at ({i},{j})"
  return applyBlockInverse p i j ps qs (1 / det) rhs

def hierarchyBlock (p : Params) (tab : PhiTable) (i j : Nat) :
    Except String (Array Rat) :=
  if i == 0 && j == 0 then pure #[1]
  else if i+j == 1 then pure #[0]
  else if i == 1 && j == 1 then
    pure #[source p tab 1 1 0 / (2+p.thetaA+p.thetaB), 0]
  else solveBlock p i j ((List.range (min i j+1)).toArray.map (source p tab i j))

def hierarchyStep (p : Params) (nb degree i : Nat) (tab : PhiTable) :
    Except String PhiTable := do
  if i > degree then return tab
  let j := degree-i
  if j > nb then return tab
  let block ← hierarchyBlock p tab i j
  return {tab with blocks := tab.blocks.set! (i*(nb+1)+j) block}

def phiTable (p : Params) (na nb : Nat) : Except String PhiTable := do
  let mut tab : PhiTable := ⟨nb, Array.replicate ((na+1)*(nb+1)) #[]⟩
  for degree in [0:na+nb+1] do
    for i in [0:na+1] do
      tab ← hierarchyStep p nb degree i tab
  return tab

abbrev Poly := Array ((Nat × Nat × Nat) × Rat)

def mulPoly (a b : Poly) : Poly := Id.run do
  let mut out : Std.HashMap (Nat × Nat × Nat) Rat := {}
  for ((i,j,t), x) in a do
    for ((k,l,u), y) in b do
      let key := (i+k,j+l,t+u)
      let v := out.getD key 0 + x*y
      out := if v == 0 then out.erase key else out.insert key v
  return out.toArray

def powPoly (a : Poly) (n : Nat) : Poly := Id.run do
  let mut out : Poly := #[((0,0,0),1)]
  for _ in [0:n] do out := mulPoly out a
  return out

def polynomial (p : Params) (c : Config) : Poly := Id.run do
  let mut out : Poly := #[((0,0,0),1)]
  for i in [0:2] do
    let sign : Rat := if i == 0 then 1 else -1
    let factor : Poly := #[((0,0,0), p.piA.getD i 0), ((1,0,0), sign)]
    for _ in [0:c.a.getD i 0] do out := mulPoly out factor
  for j in [0:2] do
    let sign : Rat := if j == 0 then 1 else -1
    let factor : Poly := #[((0,0,0), p.piB.getD j 0), ((0,1,0), sign)]
    for _ in [0:c.b.getD j 0] do out := mulPoly out factor
  for i in [0:2] do
    for j in [0:2] do
      let sa : Rat := if i == 0 then 1 else -1
      let sb : Rat := if j == 0 then 1 else -1
      let factor : Poly := #[((0,0,0), p.piA.getD i 0 * p.piB.getD j 0),
        ((1,0,0), sa*p.piB.getD j 0), ((0,1,0), p.piA.getD i 0*sb), ((1,1,1), sa*sb)]
      for _ in [0:c.c.getD (2*i+j) 0] do out := mulPoly out factor
  return out

def assemble (tab : PhiTable) (g : Poly) : Rat :=
  g.foldl (fun acc ((i,j,t), v) => acc + v*tab.get i j t) 0

def q (p : Params) (c : Config) : Except String Rat := do
  if !p.valid then throw "invalid parameters"
  if c.a.size != 2 || c.b.size != 2 || c.c.size != 4 then throw "K out of scope"
  let (na,nb) := c.block
  let tab ← phiTable p na nb
  return assemble tab (polynomial p c)

end Rhone.Computation
