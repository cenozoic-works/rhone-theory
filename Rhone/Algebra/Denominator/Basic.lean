/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-! # Clearing denominators, divisibility in a subring, and reduced denominators -/

@[expose] public section

namespace Rhone.Algebra.Denominator

variable {F : Type*} [Field F]

def Clears (A : Subring F) (x d : F) : Prop := d ∈ A ∧ d * x ∈ A

theorem Clears.mem {A : Subring F} {x d : F} (h : Clears A x d) : d ∈ A := h.1

theorem Clears.mul_mem {A : Subring F} {x d : F} (h : Clears A x d) : d * x ∈ A := h.2

theorem clears_zero (A : Subring F) (x : F) : Clears A x 0 := by
  refine ⟨A.zero_mem, ?_⟩
  rw [zero_mul]
  exact A.zero_mem

theorem clears_of_mem {A : Subring F} {x : F} (hx : x ∈ A) {d : F} (hd : d ∈ A) :
    Clears A x d :=
  ⟨hd, A.mul_mem hd hx⟩

theorem clears_add {A : Subring F} {x d d' : F} (h : Clears A x d) (h' : Clears A x d') :
    Clears A x (d + d') := by
  refine ⟨A.add_mem h.1 h'.1, ?_⟩
  rw [add_mul]
  exact A.add_mem h.2 h'.2

theorem clears_mul_left {A : Subring F} {x d : F} (h : Clears A x d) {c : F} (hc : c ∈ A) :
    Clears A x (c * d) := by
  refine ⟨A.mul_mem hc h.1, ?_⟩
  rw [mul_assoc]
  exact A.mul_mem hc h.2

def DvdIn (A : Subring F) (e x : F) : Prop := ∃ k ∈ A, x = e * k

theorem DvdIn.refl (A : Subring F) (e : F) : DvdIn A e e :=
  ⟨1, A.one_mem, (mul_one e).symm⟩

theorem DvdIn.trans {A : Subring F} {e x y : F} (h : DvdIn A e x) (h' : DvdIn A x y) :
    DvdIn A e y := by
  obtain ⟨k, hk, hx⟩ := h
  obtain ⟨l, hl, hy⟩ := h'
  exact ⟨k * l, A.mul_mem hk hl, by rw [hy, hx, mul_assoc]⟩

theorem DvdIn.mul_right {A : Subring F} {e x : F} (h : DvdIn A e x) {c : F} (hc : c ∈ A) :
    DvdIn A e (x * c) := by
  obtain ⟨k, hk, hx⟩ := h
  exact ⟨k * c, A.mul_mem hk hc, by rw [hx, mul_assoc]⟩

theorem DvdIn.mul_left {A : Subring F} {e x : F} (h : DvdIn A e x) {c : F} (hc : c ∈ A) :
    DvdIn A e (c * x) := by
  obtain ⟨k, hk, hx⟩ := h
  refine ⟨c * k, A.mul_mem hc hk, ?_⟩
  rw [hx]
  ring

theorem DvdIn.sub {A : Subring F} {e x y : F} (h : DvdIn A e x) (h' : DvdIn A e y) :
    DvdIn A e (x - y) := by
  obtain ⟨k, hk, hx⟩ := h
  obtain ⟨l, hl, hy⟩ := h'
  refine ⟨k - l, A.sub_mem hk hl, ?_⟩
  rw [hx, hy]
  ring

theorem dvdIn_mul_right (A : Subring F) {e c : F} (hc : c ∈ A) : DvdIn A e (e * c) :=
  ⟨c, hc, rfl⟩

structure IsRedDenom (A : Subring F) (x D : F) : Prop where
  clears : Clears A x D
  min : ∀ d, Clears A x d → DvdIn A D d

theorem IsRedDenom.mem {A : Subring F} {x D : F} (h : IsRedDenom A x D) : D ∈ A :=
  h.clears.1

theorem IsRedDenom.unique {A : Subring F} {x D D' : F} (h : IsRedDenom A x D)
    (h' : IsRedDenom A x D') : DvdIn A D D' ∧ DvdIn A D' D :=
  ⟨h.min D' h'.clears, h'.min D h.clears⟩

theorem dvdIn_of_isRedDenom_iff {A : Subring F} {x D e : F} (h : IsRedDenom A x D) :
    (∀ d, Clears A x d → DvdIn A e d) ↔ DvdIn A e D :=
  ⟨fun H => H D h.clears, fun H d hd => H.trans (h.min d hd)⟩

end Rhone.Algebra.Denominator
