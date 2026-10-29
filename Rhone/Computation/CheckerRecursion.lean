/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy

/-! # Direct finite sum for the biallelic recursion -/

@[expose] public section

namespace Rhone.Computation

def decrementCounts (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.setIfInBounds i (xs.getD i 0 - 1)

def incrementCounts (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.setIfInBounds i (xs.getD i 0 + 1)

def recursionRhsDirect (p : Params) (value : Config → Rat) (s : Config) : Rat :=
  let aTerm := fun i =>
    let a := s.a.getD i 0
    let row := s.c.getD (2 * i) 0 + s.c.getD (2 * i + 1) 0
    let lower := {s with a := decrementCounts s.a i}
    ((a * (a - 1 + 2 * row) : Nat) : Rat) * value lower +
      p.thetaA * p.piA.getD i 0 * (a : Rat) * value lower
  let bTerm := fun j =>
    let b := s.b.getD j 0
    let col := s.c.getD j 0 + s.c.getD (2 + j) 0
    let lower := {s with b := decrementCounts s.b j}
    ((b * (b - 1 + 2 * col) : Nat) : Rat) * value lower +
      p.thetaB * p.piB.getD j 0 * (b : Rat) * value lower
  let linkedTerm := fun i j =>
    let index := 2 * i + j
    let linked := s.c.getD index 0
    let a := s.a.getD i 0
    let b := s.b.getD j 0
    let lower := {s with c := decrementCounts s.c index}
    let joined : Config := ⟨decrementCounts s.a i, decrementCounts s.b j, incrementCounts s.c index⟩
    ((2 * a * b : Nat) : Rat) * value joined +
      ((linked * (linked - 1) : Nat) : Rat) * value lower +
      p.thetaA * p.piA.getD i 0 * (linked : Rat) *
        value {lower with b := incrementCounts s.b j} +
      p.thetaB * p.piB.getD j 0 * (linked : Rat) *
        value {lower with a := incrementCounts s.a i} +
      p.rho * (linked : Rat) *
        value {lower with a := incrementCounts s.a i, b := incrementCounts s.b j}
  aTerm 0 + aTerm 1 + bTerm 0 + bTerm 1 +
    linkedTerm 0 0 + linkedTerm 0 1 + linkedTerm 1 0 + linkedTerm 1 1

end Rhone.Computation
