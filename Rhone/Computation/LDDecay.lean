/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable linkage disequilibrium decay

Source: robbins1918, eq. (5), p. 377; lewontin_kojima1960, eq. (3), p. 459; lewontin1964, p. 50. -/

@[expose] public section
namespace Rhone.Computation.LDDecay

structure Gametes where
  x11 : Rat
  x12 : Rat
  x21 : Rat
  x22 : Rat

namespace Gametes

def total (g : Gametes) : Rat := g.x11 + g.x12 + g.x21 + g.x22

def pA (g : Gametes) : Rat := g.x11 + g.x12

def pB (g : Gametes) : Rat := g.x11 + g.x21

def pA' (g : Gametes) : Rat := g.x21 + g.x22

def pB' (g : Gametes) : Rat := g.x12 + g.x22

def D (g : Gametes) : Rat := g.x11 * g.x22 - g.x12 * g.x21

def recombine (r : Rat) (g : Gametes) : Gametes where
  x11 := (1 - r) * g.x11 + r * g.pA * g.pB
  x12 := (1 - r) * g.x12 + r * g.pA * g.pB'
  x21 := (1 - r) * g.x21 + r * g.pA' * g.pB
  x22 := (1 - r) * g.x22 + r * g.pA' * g.pB'

def recombineN (r : Rat) (g : Gametes) : Nat → Gametes
  | 0 => g
  | t + 1 => recombine r (recombineN r g t)

end Gametes

def dClosedForm (r D0 : Rat) (t : Nat) : Rat := (1 - r) ^ t * D0

def dMax (pA pB D : Rat) : Rat :=
  if 0 ≤ D then
    (if pA * (1 - pB) ≤ (1 - pA) * pB then pA * (1 - pB) else (1 - pA) * pB)
  else
    (if pA * pB ≤ (1 - pA) * (1 - pB) then pA * pB else (1 - pA) * (1 - pB))

def lewontinD' (pA pB D : Rat) : Rat := D / dMax pA pB D

def rSq (pA pB D : Rat) : Rat := D ^ 2 / (pA * (1 - pA) * pB * (1 - pB))

end Rhone.Computation.LDDecay
