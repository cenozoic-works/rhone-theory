/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable breeder's equation

Source: lush1943, ch. 12, p. 143; felsenstein_teg2019, eq. (IX-69), p. 443; falconer_mackay1996,
ch. 11. -/

@[expose] public section
namespace Rhone.Computation.Breeders

def heritability (VA VP : Rat) : Option Rat :=
  if VP = 0 then none else some (VA / VP)

def response (VA VP S : Rat) : Option Rat :=
  if VP = 0 then none else some (VA / VP * S)

end Rhone.Computation.Breeders
