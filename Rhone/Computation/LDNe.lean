/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat
public import Rhone.Computation.OhtaKimura

/-!
# Executable sampling matrix and correction for LD-based effective size

Source: hill1981, eq. (1)–(3), pp. 210–211. -/

@[expose] public section
namespace Rhone.Computation.LDNe

structure Mom where
  h : Rat
  z : Rat
  d : Rat

def samplingMoment (S : Rat) (v : Mom) : Mom where
  h := (S - 1) ^ 2 / S ^ 2 * v.h + (S - 1) ^ 2 / S ^ 3 * v.z + 2 * (S - 1) / S ^ 3 * v.d
  z := (S - 2) ^ 2 * (S - 1) / S ^ 3 * v.z + 4 * (S - 2) * (S - 1) / S ^ 3 * v.d
  d := (S - 1) / S ^ 2 * v.h + (S - 1) ^ 2 / S ^ 3 * v.z +
    (S - 1) * (S ^ 2 - 2 * S + 2) / S ^ 3 * v.d

def samplingCorrection (S : Rat) (v : Mom) : Mom where
  h := S / ((S - 1) * (S - 2) * (S - 3)) *
    ((S ^ 2 - 4 * S + 2) * v.h + (-(S - 1)) * v.z + 2 * v.d)
  z := S / ((S - 1) * (S - 2) * (S - 3)) *
    (4 * v.h + (S ^ 2 - S + 2) * v.z + (-(4 * (S - 1))) * v.d)
  d := S / ((S - 1) * (S - 2) * (S - 3)) *
    ((-(S - 2)) * v.h + (-(S - 1)) * v.z + ((S - 1) * (S - 2)) * v.d)

def correctedRatio (S : Rat) (v : Mom) : Rat :=
  (samplingCorrection S v).d / (samplingCorrection S v).h

end Rhone.Computation.LDNe
