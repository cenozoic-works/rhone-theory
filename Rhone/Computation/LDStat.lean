/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable linkage disequilibrium measures

Source: lewontin_kojima1960, eq. (2), p. 459; lewontin1964, p. 50; lewontin1964, pp. 54–55;
hill_robertson1968, p. 226; hill1981, p. 210. -/

@[expose] public section
namespace Rhone.Computation.LDStat

structure Hap where
  x11 : Rat
  x12 : Rat
  x21 : Rat
  x22 : Rat

def pA (g : Hap) : Rat := g.x11 + g.x12

def pB (g : Hap) : Rat := g.x11 + g.x21

def total (g : Hap) : Rat := g.x11 + g.x12 + g.x21 + g.x22

def ldD (g : Hap) : Rat := g.x11 * g.x22 - g.x12 * g.x21

def dMax (pA pB D : Rat) : Rat :=
  if 0 ≤ D then min (pA * (1 - pB)) ((1 - pA) * pB) else min (pA * pB) ((1 - pA) * (1 - pB))

def lewontinD' (pA pB D : Rat) : Rat := D / dMax pA pB D

def rSq (pA pB D : Rat) : Rat := D * D / (pA * (1 - pA) * pB * (1 - pB))

def ldDPrime (g : Hap) : Rat := lewontinD' (pA g) (pB g) (ldD g)

def ldRSq (g : Hap) : Rat := rSq (pA g) (pB g) (ldD g)

end Rhone.Computation.LDStat
