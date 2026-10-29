/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable single-locus additive and dominance variance and covariances of relatives

Source: fisher1918, pp. 404–406, eq. V–XI; kempthorne1954, pp. 106–107, 112; felsenstein_teg2019,
sec. IX.5, eq. (IX-51)–(IX-55), pp. 428–429; falconer_mackay1996, chs. 7–9. -/

@[expose] public section
namespace Rhone.Computation.QuantCovariance

structure Values where
  g0 : Rat
  g1 : Rat
  g2 : Rat

def Values.get (G : Values) : Nat → Rat
  | 0 => G.g0
  | 1 => G.g1
  | _ => G.g2

def hwExp (p : Rat) (f0 f1 f2 : Rat) : Rat :=
  (1 - p) ^ 2 * f0 + 2 * p * (1 - p) * f1 + p ^ 2 * f2

def genoMean (p : Rat) (G : Values) : Rat := hwExp p G.g0 G.g1 G.g2

def avgEffect (p : Rat) (G : Values) : Rat :=
  (G.g2 - G.g0) / 2 + (G.g1 - (G.g2 + G.g0) / 2) * ((1 - p) - p)

def breedingValue (p : Rat) (G : Values) (k : Nat) : Rat := ((k : Rat) - 2 * p) * avgEffect p G

def domDev (p : Rat) (G : Values) (k : Nat) : Rat :=
  G.get k - genoMean p G - breedingValue p G k

def varARaw (p : Rat) (G : Values) : Rat :=
  hwExp p (breedingValue p G 0 ^ 2) (breedingValue p G 1 ^ 2) (breedingValue p G 2 ^ 2)

def varDRaw (p : Rat) (G : Values) : Rat :=
  hwExp p (domDev p G 0 ^ 2) (domDev p G 1 ^ 2) (domDev p G 2 ^ 2)

def sharedAlleleProduct (p : Rat) (G : Values) : Rat :=
  (1 - p) * ((1 - p) * G.g0 + p * G.g1) * ((1 - p) * G.g0 + p * G.g1) +
  p * ((1 - p) * G.g1 + p * G.g2) * ((1 - p) * G.g1 + p * G.g2)

def validFreq (p : Rat) : Bool := decide (0 ≤ p ∧ p ≤ 1)

def varA (p : Rat) (G : Values) : Option Rat :=
  if validFreq p then some (varARaw p G) else none

def varD (p : Rat) (G : Values) : Option Rat :=
  if validFreq p then some (varDRaw p G) else none

def parentOffspringCov (p : Rat) (G : Values) : Option Rat :=
  if validFreq p then some (sharedAlleleProduct p G - genoMean p G * genoMean p G) else none

def halfSibCov (p : Rat) (G : Values) : Option Rat :=
  if validFreq p then
    some ((genoMean p G ^ 2 + sharedAlleleProduct p G) / 2 - genoMean p G ^ 2)
  else none

def fullSibCov (p : Rat) (G : Values) : Option Rat :=
  if validFreq p then
    some ((genoMean p G ^ 2 + 2 * sharedAlleleProduct p G +
      hwExp p (G.g0 ^ 2) (G.g1 ^ 2) (G.g2 ^ 2)) / 4 - genoMean p G ^ 2)
  else none

end Rhone.Computation.QuantCovariance
