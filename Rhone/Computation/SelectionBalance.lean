/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable mutation-selection and migration-selection balance

Source: haldane1927, pp. 840–841, eq. (2.0); felsenstein_teg2019, sec. III.5, eq. (III-18), p. 147,
eq. (III-23), p. 150; crow_kimura1970, sec. 6.5; burger2013_migration_selection, sec. 4. -/

@[expose] public section
namespace Rhone.Computation.SelectionBalance

def hapMutSelStep (s mu q : Rat) : Rat := mu + (1 - mu) * (q * (1 - s) / (1 - s * q))

def hapEquilibrium (s mu : Rat) : Rat := mu / s

def dipMutSelStep (h s mu q : Rat) : Rat :=
  mu + (1 - mu) * (q * (1 - h * s * (1 - q) - s * q) /
    (1 - 2 * h * s * q * (1 - q) - s * q ^ 2))

def dipMeanFit (h s q : Rat) : Rat := 1 - 2 * h * s * q * (1 - q) - s * q ^ 2

def dipFixedResidual (h s mu q : Rat) : Rat :=
  s * q ^ 2 + h * s * q * (1 + mu - 2 * q) - mu

def dipFixedCandidate (h s mu q : Rat) : Bool :=
  decide (q = 1 ∨ dipFixedResidual h s mu q = 0)

def recessiveEquilibriumSq (s mu : Rat) : Rat := mu / s

def islandGenicStep (s m p : Rat) : Rat := (1 - m) * p / (1 - s + s * p)

def islandPositiveEquilibrium (s m : Rat) : Option Rat :=
  if m < s then some (1 - m / s) else none

def twoDemeFirst (s m p q : Rat) : Rat :=
  (1 - m) * (1 + s) * p / (1 + s * p) + m * q / (1 + s * (1 - q))

def twoDemeSecond (s m p q : Rat) : Rat :=
  m * (1 + s) * p / (1 + s * p) + (1 - m) * q / (1 + s * (1 - q))

def twoDemeQuadratic (s m p : Rat) : Rat := s * p ^ 2 + (2 * m + m * s - s) * p - m

def twoDemeDiscriminant (s m : Rat) : Rat := (s - 2 * m - m * s) ^ 2 + 4 * s * m

end Rhone.Computation.SelectionBalance
