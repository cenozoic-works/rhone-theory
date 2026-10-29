/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Executable moments of the temporal change in allele frequency -/

@[expose] public section
namespace Rhone.Computation.TemporalNe

def retention (N t : Nat) : Rat := (1 - 1 / (N : Rat)) ^ t

def p0 (N i : Nat) : Rat := (i : Rat) / (N : Rat)

def driftSecondMoment (N t i : Nat) : Rat :=
  p0 N i * (1 - p0 N i) * (1 - retention N t)

def standardizedDrift (N t : Nat) : Rat := 1 - retention N t

def expectedFrequencyHet (N t i : Nat) : Rat := retention N t * (p0 N i * (1 - p0 N i))

def sampledMsd (N t S0 St i : Nat) : Rat :=
  p0 N i * (1 - p0 N i) *
    ((1 - retention N t) + 1 / (S0 : Rat) + retention N t / (St : Rat))

end Rhone.Computation.TemporalNe
