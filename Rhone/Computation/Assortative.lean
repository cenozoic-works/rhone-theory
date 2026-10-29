/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable assortative mating

Source: crow_kimura1970, sec. 4.6, p. 144. -/

@[expose] public section
namespace Rhone.Computation.Assortative

def assortFreq (g : Rat × Rat × Rat) : Rat := g.1 + g.2.1 / 2

def assortStep (α : Rat) (g : Rat × Rat × Rat) : Rat × Rat × Rat :=
  ((1 - α) * assortFreq g ^ 2 + α * (g.1 + g.2.1 / 4),
    (1 - α) * (2 * assortFreq g * (1 - assortFreq g)) + α * (g.2.1 / 2),
    (1 - α) * (1 - assortFreq g) ^ 2 + α * (g.2.2 + g.2.1 / 4))

def assortOrbit (α : Rat) (g0 : Rat × Rat × Rat) : Nat → Rat × Rat × Rat
  | 0 => g0
  | t + 1 => assortStep α (assortOrbit α g0 t)

def assortHetFixed (α p : Rat) : Rat := 4 * p * (1 - p) * (1 - α) / (2 - α)

def hetClosed (α : Rat) (g0 : Rat × Rat × Rat) (t : Nat) : Rat :=
  assortHetFixed α (assortFreq g0) +
    (α / 2) ^ t * (g0.2.1 - assortHetFixed α (assortFreq g0))

end Rhone.Computation.Assortative
