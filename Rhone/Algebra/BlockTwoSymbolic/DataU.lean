/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Data

/-! # The `u`-last division certificate for the block-`(2,2)` numerator at symbolic `pi` -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

variable {R : Type*} [CommRing R]

def E22uOf (u r : R) : R :=
  2 * u ^ 3 + (3 * r + 20) * u ^ 2 + (r ^ 2 + 19 * r + 54) * u + (2 * r ^ 2 + 26 * r + 36)

def HqU (u v a b r : R) : R :=
  u ^ 2 * a ^ 2 * b ^ 2 - 2 * u ^ 2 * a ^ 2 * b + u ^ 2 * a ^ 2 - 2 * u ^ 2 * a * b ^ 2 + 4 * u ^
    2 * a * b - 2 * u ^ 2 * a + u ^ 2 * b ^ 2 - 2 * u ^ 2 * b + u ^ 2 + u * a ^ 2 * b ^ 2 - 3 * u
    * a ^ 2 * b + 2 * u * a ^ 2 - 3 * u * a * b ^ 2 + 9 * u * a * b - 6 * u * a + 2 * u * b ^ 2 -
    6 * u * b + 4 * u - v ^ 2 * a ^ 2 * b ^ 2 + 2 * v ^ 2 * a ^ 2 * b - v ^ 2 * a ^ 2 + 2 * v ^ 2
    * a * b ^ 2 - 4 * v ^ 2 * a * b + 2 * v ^ 2 * a - v ^ 2 * b ^ 2 + 2 * v ^ 2 * b - v ^ 2 - 2 *
    v * a ^ 2 * b + 2 * v * a ^ 2 + 2 * v * a * b ^ 2 - 2 * v * a - 2 * v * b ^ 2 + 2 * v * b - a
    ^ 2 * b ^ 2 * r - a ^ 2 * b ^ 2 + a ^ 2 * b * r + a ^ 2 * b + a * b ^ 2 * r + a * b ^ 2 - a *
    b * r + 3 * a * b - 4 * a - 4 * b + 4

def RemU2 (v a b r : R) : R :=
  -2 * v ^ 2 * a ^ 2 * b ^ 2 + 2 * v ^ 2 * a ^ 2 * b + 2 * v ^ 2 * a * b ^ 2 - 2 * v ^ 2 * a * b +
    2 * a ^ 2 * b ^ 2 * r ^ 2 + 6 * a ^ 2 * b ^ 2 * r + 2 * a ^ 2 * b ^ 2 - 2 * a ^ 2 * b * r ^ 2
    - 6 * a ^ 2 * b * r - 2 * a ^ 2 * b - 2 * a * b ^ 2 * r ^ 2 - 6 * a * b ^ 2 * r - 2 * a * b ^
    2 + 2 * a * b * r ^ 2 + 6 * a * b * r + 2 * a * b

def RemU1 (v a b r : R) : R :=
  -v ^ 2 * a ^ 2 * b ^ 2 * r - 18 * v ^ 2 * a ^ 2 * b ^ 2 + v ^ 2 * a ^ 2 * b * r + 18 * v ^ 2 * a
    ^ 2 * b + v ^ 2 * a * b ^ 2 * r + 18 * v ^ 2 * a * b ^ 2 - v ^ 2 * a * b * r - 18 * v ^ 2 * a
    * b + a ^ 2 * b ^ 2 * r ^ 3 + 18 * a ^ 2 * b ^ 2 * r ^ 2 + 47 * a ^ 2 * b ^ 2 * r + 18 * a ^ 2
    * b ^ 2 - a ^ 2 * b * r ^ 3 - 18 * a ^ 2 * b * r ^ 2 - 47 * a ^ 2 * b * r - 18 * a ^ 2 * b - a
    * b ^ 2 * r ^ 3 - 18 * a * b ^ 2 * r ^ 2 - 47 * a * b ^ 2 * r - 18 * a * b ^ 2 + a * b * r ^ 3
    + 18 * a * b * r ^ 2 + 47 * a * b * r + 18 * a * b

def RemU0 (v a b r : R) : R :=
  -2 * v ^ 2 * a ^ 2 * b ^ 2 * r - 36 * v ^ 2 * a ^ 2 * b ^ 2 + 2 * v ^ 2 * a ^ 2 * b * r + 36 * v
    ^ 2 * a ^ 2 * b + 2 * v ^ 2 * a * b ^ 2 * r + 36 * v ^ 2 * a * b ^ 2 - 2 * v ^ 2 * a * b * r -
    36 * v ^ 2 * a * b + 2 * a ^ 2 * b ^ 2 * r ^ 3 + 28 * a ^ 2 * b ^ 2 * r ^ 2 + 62 * a ^ 2 * b ^
    2 * r + 36 * a ^ 2 * b ^ 2 - 2 * a ^ 2 * b * r ^ 3 - 28 * a ^ 2 * b * r ^ 2 - 62 * a ^ 2 * b *
    r - 36 * a ^ 2 * b - 2 * a * b ^ 2 * r ^ 3 - 28 * a * b ^ 2 * r ^ 2 - 62 * a * b ^ 2 * r - 36
    * a * b ^ 2 + 2 * a * b * r ^ 3 + 28 * a * b * r ^ 2 + 62 * a * b * r + 36 * a * b

def RemU (u v a b r : R) : R :=
  RemU2 v a b r * u ^ 2 + RemU1 v a b r * u + RemU0 v a b r

section Naturality

variable {S : Type*} [CommRing S] (f : R →+* S) (v a b r : R)

theorem RemU2_map : f (RemU2 v a b r) = RemU2 (f v) (f a) (f b) (f r) := by
  simp only [RemU2, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem RemU1_map : f (RemU1 v a b r) = RemU1 (f v) (f a) (f b) (f r) := by
  simp only [RemU1, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem RemU0_map : f (RemU0 v a b r) = RemU0 (f v) (f a) (f b) (f r) := by
  simp only [RemU0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

end Naturality

end Rhone.Algebra.BlockTwoSymbolic
