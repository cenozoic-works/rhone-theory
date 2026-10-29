/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64FiniteNearest
public import Rhone.Computation.Binary64Encode
/-! # Bounded zero and positive normal binary64 acceptance -/

@[expose] public section
namespace Rhone.Computation.Binary64Scientific

def accepted (x : Rat) (bits : Nat) (e : Int) : Bool :=
  decide (x = 0 ∧ bits = 0) || Binary64Normal.acceptedPositive x bits e

def emit (x : Rat) (e : Int) : Option Nat :=
  if x = 0 then some 0 else Binary64Encode.emit x e

lemma normal_decode_finite {bits : Nat} {y : Rat}
    (h : Binary64Normal.decode bits = some y) :
    Binary64FiniteNearest.decodeFinite bits = some y := by
  have hdom : bits < 2 ^ 64 ∧ 1 ≤ bits / 2 ^ 52 % 2048 ∧ bits / 2 ^ 52 % 2048 ≤ 2046 := by
    dsimp only [Binary64Normal.decode] at h
    split_ifs at h with hv hs <;> exact hv
  have hb : bits / 2 ^ 52 % 2048 < 2047 := by omega
  have hn : bits / 2 ^ 52 % 2048 ≠ 0 := by omega
  dsimp only [Binary64FiniteNearest.decodeFinite]
  rw [ite_eq_left ⟨hdom.1, hb⟩, ite_eq_right hn]
  exact h

lemma emit_accepts {x : Rat} {e : Int} {bits : Nat} (h : emit x e = some bits) :
    accepted x bits e = true := by
  dsimp only [emit] at h
  split_ifs at h with hz
  · have hb : bits = 0 := (Option.some.inj h).symm
    simp [accepted, hz, hb]
  · have ha := Binary64Encode.emit_accepts h
    simp [accepted, ha]

lemma accepted_nearest {x y z : Rat} {e : Int} {bits other : Nat}
    (h : accepted x bits e = true)
    (hy : Binary64FiniteNearest.decodeFinite bits = some y)
    (hz : Binary64FiniteNearest.decodeFinite other = some z) : |y - x| ≤ |z - x| := by
  simp only [accepted, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hx, hb⟩ | hn
  · subst x; subst bits
    have hd : Binary64FiniteNearest.decodeFinite 0 = some 0 := by
      norm_num [Binary64FiniteNearest.decodeFinite]
    rw [hd] at hy
    have he : y = 0 := (Option.some.inj hy).symm
    rw [he]
    simp
  · have hd := Binary64Normal.acceptedPositive_decode hn
    have hf := normal_decode_finite hd
    rw [hy] at hf
    have he : y = RatRounding.quantize ((2 : Rat) ^ (e - 52)) x := Option.some.inj hf
    exact Binary64FiniteNearest.accepted_finite_nearest hn (he.symm ▸ hd) hz

lemma accepted_relative {x y : Rat} {e : Int} {bits : Nat}
    (h : accepted x bits e = true)
    (hy : Binary64FiniteNearest.decodeFinite bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 := by
  simp only [accepted, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hx, _⟩ | hn
  · subst x
    norm_num
  · have hd := Binary64Normal.acceptedPositive_decode hn
    have hf := normal_decode_finite hd
    rw [hy] at hf
    have he : y = RatRounding.quantize ((2 : Rat) ^ (e - 52)) x := Option.some.inj hf
    exact Binary64Normal.acceptedPositive_relative hn (he.symm ▸ hd)

def guardedAccepted (x : Rat) (bits : Nat) (e : Int) : Bool :=
  if x = 0 then decide (bits = 0)
  else if e < -1023 ∨ 1023 < e then false
  else accepted x bits e

lemma guarded_sound {x : Rat} {bits : Nat} {e : Int}
    (h : guardedAccepted x bits e = true) : accepted x bits e = true := by
  dsimp only [guardedAccepted] at h
  split_ifs at h with hz hout
  · simp only [decide_eq_true_eq] at h
    simp [accepted, hz, h]
  · exact h

lemma guarded_outside_refuses {x : Rat} {bits : Nat} {e : Int} (hx : x ≠ 0)
    (he : e < -1023 ∨ 1023 < e) : guardedAccepted x bits e = false := by
  simp [guardedAccepted, hx, he]

lemma guarded_nearest {x y z : Rat} {e : Int} {bits other : Nat}
    (h : guardedAccepted x bits e = true)
    (hy : Binary64FiniteNearest.decodeFinite bits = some y)
    (hz : Binary64FiniteNearest.decodeFinite other = some z) : |y - x| ≤ |z - x| :=
  accepted_nearest (guarded_sound h) hy hz

lemma guarded_relative {x y : Rat} {e : Int} {bits : Nat}
    (h : guardedAccepted x bits e = true)
    (hy : Binary64FiniteNearest.decodeFinite bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 :=
  accepted_relative (guarded_sound h) hy

end Rhone.Computation.Binary64Scientific
