/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Normal
/-! # Guarded positive normal binary64 word emission -/

@[expose] public section
namespace Rhone.Computation.Binary64Encode

def word (x : Rat) (e : Int) : Nat :=
  let m := Rhone.Computation.RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52))
  let carried := m = (2 : Int) ^ 53
  let finalExponent := if carried then e + 1 else e
  let finalMantissa := if carried then (2 : Int) ^ 52 else m
  Binary64Normal.encode false (finalExponent + 1023).toNat
    (finalMantissa - 2 ^ 52).toNat

def emit (x : Rat) (e : Int) : Option Nat :=
  if e < -1023 ∨ 1023 < e then none else
  if Binary64Normal.acceptedPositive x (word x e) e then some (word x e) else none

lemma emit_accepts {x : Rat} {e : Int} {bits : Nat} (h : emit x e = some bits) :
    Binary64Normal.acceptedPositive x bits e = true := by
  dsimp only [emit] at h
  split_ifs at h with houtside haccepted
  · exact (Option.some.inj h) ▸ haccepted

lemma emit_relative {x y : Rat} {e : Int} {bits : Nat} (h : emit x e = some bits)
    (hd : Binary64Normal.decode bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 :=
  Binary64Normal.acceptedPositive_relative (emit_accepts h) hd

lemma emit_grid_nearest {x y : Rat} {e : Int} {bits : Nat} (h : emit x e = some bits)
    (hd : Binary64Normal.decode bits = some y) (k : Int) :
    |y - x| ≤ |(2 : Rat) ^ (e - 52) * k - x| :=
  Binary64Normal.acceptedPositive_grid_nearest (emit_accepts h) hd k

lemma emit_exponent_refuses {x : Rat} {e : Int} (h : e < -1023 ∨ 1023 < e) :
    emit x e = none := by simp [emit, h]

end Rhone.Computation.Binary64Encode
