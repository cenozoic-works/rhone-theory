/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable X-linked approach to equilibrium

Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/

@[expose] public section
namespace Rhone.Computation.XLinked

def xStep (x : Rat × Rat) : Rat × Rat := ((x.1 + x.2) / 2, x.1)

def xOrbit (f0 m0 : Rat) : Nat → Rat × Rat
  | 0 => (f0, m0)
  | t + 1 => xStep (xOrbit f0 m0 t)

def weightedMean (x : Rat × Rat) : Rat := (2 * x.1 + x.2) / 3

def fClosed (f0 m0 : Rat) (t : Nat) : Rat :=
  (2 * f0 + m0) / 3 + (1 / 3) * (-1 / 2) ^ t * (f0 - m0)

def mClosed (f0 m0 : Rat) (t : Nat) : Rat :=
  (2 * f0 + m0) / 3 - (2 / 3) * (-1 / 2) ^ t * (f0 - m0)

end Rhone.Computation.XLinked
