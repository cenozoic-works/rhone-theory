/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Rhone.Computation.CheckerRecursion
public import Rhone.Computation.Closure
public import Rhone.Computation.CheckerRows

/-! # Exact finite-closure table checks -/

@[expose] public section
namespace Rhone.Computation

def decrement (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.set! i (xs.getD i 0 - 1)

def increment (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.set! i (xs.getD i 0 + 1)

def recursionRhsLoop (p : Params) (value : Config → Rat) (s : Config) : Rat := Id.run do
  let mut acc : Rat := 0
  for i in [0:2] do
    let a := s.a.getD i 0
    if a > 0 then
      let lower := {s with a := decrement s.a i}
      acc := acc + ((a*(a-1) : Nat) : Rat)*value lower
      acc := acc + p.thetaA*p.piA.getD i 0*(a : Rat)*value lower
    for j in [0:2] do
      let c := s.c.getD (2*i+j) 0
      if a > 0 && c > 0 then
        acc := acc + ((2*a*c : Nat) : Rat)*value {s with a := decrement s.a i}
  for j in [0:2] do
    let b := s.b.getD j 0
    if b > 0 then
      let lower := {s with b := decrement s.b j}
      acc := acc + ((b*(b-1) : Nat) : Rat)*value lower
      acc := acc + p.thetaB*p.piB.getD j 0*(b : Rat)*value lower
    for i in [0:2] do
      let c := s.c.getD (2*i+j) 0
      if b > 0 && c > 0 then
        acc := acc + ((2*b*c : Nat) : Rat)*value {s with b := decrement s.b j}
  for i in [0:2] do
    for j in [0:2] do
      let index := 2*i+j
      let linked := s.c.getD index 0
      let a := s.a.getD i 0
      let b := s.b.getD j 0
      if a > 0 && b > 0 then
        let joined : Config := ⟨decrement s.a i, decrement s.b j, increment s.c index⟩
        acc := acc + ((2*a*b : Nat) : Rat)*value joined
      if linked > 0 then
        let lower := {s with c := decrement s.c index}
        acc := acc + ((linked*(linked-1) : Nat) : Rat)*value lower
        acc := acc + p.thetaA*p.piA.getD i 0*(linked : Rat)*
          value {lower with b := increment s.b j}
        acc := acc + p.thetaB*p.piB.getD j 0*(linked : Rat)*
          value {lower with a := increment s.a i}
        acc := acc + p.rho*(linked : Rat)*
          value {lower with a := increment s.a i, b := increment s.b j}
  return acc

def recursionRhs (p : Params) (value : Config → Rat) (s : Config) : Rat :=
  recursionRhsDirect p value s

def factorial (n : Nat) : Nat := rangeProduct 0 n

def checkerLineages (s : Config) : Nat :=
  s.a.foldl (· + ·) 0 + s.b.foldl (· + ·) 0 + s.c.foldl (· + ·) 0

def checkerBoundary (p : Params) (s : Config) : Rat :=
  (s.a.getD 0 0 : Rat) * p.piA.getD 0 0 +
  (s.a.getD 1 0 : Rat) * p.piA.getD 1 0 +
  (s.b.getD 0 0 : Rat) * p.piB.getD 0 0 +
  (s.b.getD 1 0 : Rat) * p.piB.getD 1 0 +
  (s.c.getD 0 0 : Rat) * p.piA.getD 0 0 * p.piB.getD 0 0 +
  (s.c.getD 1 0 : Rat) * p.piA.getD 0 0 * p.piB.getD 1 0 +
  (s.c.getD 2 0 : Rat) * p.piA.getD 1 0 * p.piB.getD 0 0 +
  (s.c.getD 3 0 : Rat) * p.piA.getD 1 0 * p.piB.getD 1 0

def checkerDiagonal (p : Params) (s : Config) : Rat :=
  let total := checkerLineages s
  let (na, nb) := s.block
  let t : Nat := s.c.foldl (· + ·) 0
  ((total * (total - 1) : Nat) : Rat) + (na : Rat) * p.thetaA +
    (nb : Rat) * p.thetaB + (t : Rat) * p.rho

def checkerEquation (p : Params) (value : Config → Rat) (s : Config) : Bool :=
  (if checkerLineages s == 1 then value s == checkerBoundary p s else true) &&
    (if checkerLineages s ≥ 2 then
      checkerDiagonal p s * value s == recursionRhs p value s else true)

def checkerNormalization (value : Config → Rat) (states : Array Config) (size : Nat) : Rat :=
  states.foldl (fun mass s =>
    if s.a.all (· == 0) && s.b.all (· == 0) && s.block == (size, size) then
      let denominator := s.c.foldl (fun z count => z * factorial count) 1
      mass + ((factorial size : Rat) / (denominator : Rat)) * value s
    else mass) 0

def checkTable (p : Params) (n : Nat) (entries : Array (Config × Rat)) : Bool :=
  if !p.valid then false else
    match insertTableRows n entries.toList {} with
    | none => false
    | some table =>
      let states := closure n
      let value := fun s => table.getD s.key 0
      entries.size == states.size &&
        states.all (fun s => table.contains s.key) &&
        value (configOfCounts 0 0 0 0 0 0 0 0) == 1 &&
        states.all (checkerEquation p value) &&
        (List.range (n + 1)).all (fun size => checkerNormalization value states size == 1)

end Rhone.Computation
