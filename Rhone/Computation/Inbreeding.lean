/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable scalar inbreeding recurrences

Source: wright1931, pp. 108–110; felsenstein1971, pp. 584–585. -/
@[expose] public section
namespace Rhone.Computation.Inbreeding

def partialStep (s F : Rat) : Rat := s * (1 + F) / 2
def partialOrbit (s F0 : Rat) : Nat → Rat
  | 0 => F0
  | n + 1 => partialStep s (partialOrbit s F0 n)
def partialFixed (s : Rat) : Rat := s / (2 - s)
def fullSibStep (z : Rat × Rat) : Rat × Rat := (z.2, (1 + 2 * z.2 + z.1) / 4)
def fullSibOrbit (z : Rat × Rat) : Nat → Rat × Rat
  | 0 => z
  | n + 1 => fullSibStep (fullSibOrbit z n)
def consecutiveEffective (F0 F1 : Rat) : Option Rat :=
  if 0 ≤ F0 ∧ F0 < F1 ∧ F1 ≤ 1 then some (1 / (2 * ((F1 - F0) / (1 - F0)))) else none

end Rhone.Computation.Inbreeding
