/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GenericField.E22

/-! # The block-`(2,2)` value `q22` with symbolic mutant frequencies -/

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

variable {R : Type*} [CommRing R]

def qM2 (u v a b : R) : R :=
  u ^ 3 * a * b - u ^ 3 * a - u ^ 3 * b + u ^ 3 + 2 * u ^ 2 * a * b - 4 * u ^ 2 * a - 4 * u ^
    2 * b + 6 * u ^ 2 - u * v ^ 2 * a * b + u * v ^ 2 * a + u * v ^ 2 * b - u * v ^ 2 - 2 *
    u * v * a + 2 * u * v * b - 4 * u * a - 4 * u * b + 12 * u - 2 * v ^ 2 * a * b + 2 * v ^
    2 * a + 2 * v ^ 2 * b - 2 * v ^ 2 - 4 * v * a + 4 * v * b + 8

def qM1 (u v a b : R) : R :=
  3 * u ^ 4 * a * b - 3 * u ^ 4 * a - 3 * u ^ 4 * b + 3 * u ^ 4 + 20 * u ^ 3 * a * b - 25 * u
    ^ 3 * a - 25 * u ^ 3 * b + 31 * u ^ 3 - 3 * u ^ 2 * v ^ 2 * a * b + 3 * u ^ 2 * v ^ 2 *
    a + 3 * u ^ 2 * v ^ 2 * b - 3 * u ^ 2 * v ^ 2 - 6 * u ^ 2 * v * a + 6 * u ^ 2 * v * b +
    28 * u ^ 2 * a * b - 64 * u ^ 2 * a - 64 * u ^ 2 * b + 114 * u ^ 2 - 20 * u * v ^ 2 * a
    * b + 19 * u * v ^ 2 * a + 19 * u * v ^ 2 * b - 19 * u * v ^ 2 - 38 * u * v * a + 38 * u
    * v * b - 52 * u * a - 52 * u * b + 180 * u - 28 * v ^ 2 * a * b + 26 * v ^ 2 * a + 26 *
    v ^ 2 * b - 26 * v ^ 2 - 52 * v * a + 52 * v * b + 104

def qM0 (u v a b : R) : R :=
  2 * u ^ 5 * a * b - 2 * u ^ 5 * a - 2 * u ^ 5 * b + 2 * u ^ 5 + 22 * u ^ 4 * a * b - 24 * u
    ^ 4 * a - 24 * u ^ 4 * b + 28 * u ^ 4 - 2 * u ^ 3 * v ^ 2 * a * b + 2 * u ^ 3 * v ^ 2 *
    a + 2 * u ^ 3 * v ^ 2 * b - 2 * u ^ 3 * v ^ 2 - 4 * u ^ 3 * v * a + 4 * u ^ 3 * v * b +
    72 * u ^ 3 * a * b - 94 * u ^ 3 * a - 94 * u ^ 3 * b + 142 * u ^ 3 - 22 * u ^ 2 * v ^ 2
    * a * b + 20 * u ^ 2 * v ^ 2 * a + 20 * u ^ 2 * v ^ 2 * b - 20 * u ^ 2 * v ^ 2 - 40 * u
    ^ 2 * v * a + 40 * u ^ 2 * v * b + 72 * u ^ 2 * a * b - 144 * u ^ 2 * a - 144 * u ^ 2 *
    b + 332 * u ^ 2 - 72 * u * v ^ 2 * a * b + 54 * u * v ^ 2 * a + 54 * u * v ^ 2 * b - 54
    * u * v ^ 2 - 108 * u * v * a + 108 * u * v * b - 72 * u * a - 72 * u * b + 360 * u - 72
    * v ^ 2 * a * b + 36 * v ^ 2 * a + 36 * v ^ 2 * b - 36 * v ^ 2 - 72 * v * a + 72 * v * b
    + 144

def qD2 (u v _a _b : R) : R :=
  u ^ 3 + 6 * u ^ 2 - u * v ^ 2 + 12 * u - 2 * v ^ 2 + 8

def qD1 (u v _a _b : R) : R :=
  3 * u ^ 4 + 31 * u ^ 3 - 3 * u ^ 2 * v ^ 2 + 114 * u ^ 2 - 19 * u * v ^ 2 + 180 * u - 26 * v
    ^ 2 + 104

def qD0 (u v _a _b : R) : R :=
  2 * u ^ 5 + 28 * u ^ 4 - 2 * u ^ 3 * v ^ 2 + 142 * u ^ 3 - 20 * u ^ 2 * v ^ 2 + 332 * u ^ 2
    - 54 * u * v ^ 2 + 360 * u - 36 * v ^ 2 + 144

def qG (u v _a _b : R) : R :=
  u ^ 2 + 4 * u - v ^ 2 + 4

def qQ (u v a b : R) : R :=
  u ^ 2 * a * b - u ^ 2 * a - u ^ 2 * b + u ^ 2 - 2 * u * a - 2 * u * b + 4 * u - v ^ 2 * a *
    b + v ^ 2 * a + v ^ 2 * b - v ^ 2 - 2 * v * a + 2 * v * b + 4

def qS1 (u v a b : R) : R :=
  u ^ 3 * a * b + 2 * u ^ 2 * a * b - u * v ^ 2 * a * b - 2 * v ^ 2 * a * b

def qS0 (u v a b : R) : R :=
  2 * u ^ 4 * a * b + 18 * u ^ 3 * a * b - 2 * u ^ 2 * v ^ 2 * a * b + 36 * u ^ 2 * a * b - 18
    * u * v ^ 2 * a * b - 36 * v ^ 2 * a * b

noncomputable def MqOf (u v a b : R) : Polynomial R :=
  C (qM2 u v a b) * X ^ 2 + C (qM1 u v a b) * X + C (qM0 u v a b)

noncomputable def NqOf (u v a b : R) : Polynomial R := C ((a - 1) * (b - 1)) * MqOf u v a b

noncomputable def DqOf (u v a b : R) : Polynomial R :=
  C (qD2 u v a b) * X ^ 2 + C (qD1 u v a b) * X + C (qD0 u v a b)

noncomputable def SqOf (u v a b : R) : Polynomial R := C (qS1 u v a b) * X + C (qS0 u v a b)

end Rhone.Algebra.SymbolicFrequencies
