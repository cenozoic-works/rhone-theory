/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Linkage disequilibrium and its decay under recombination

Source: lewontin_kojima1960, eq. (2)–(3), p. 459; lewontin1964, p. 50; robbins1918, eq. (5), p. 377;
crow_kimura1970, §2.4. -/

@[expose] public section

namespace Rhone.Dynamics

structure Gametes (F : Type*) where
  x11 : F
  x12 : F
  x21 : F
  x22 : F

namespace Gametes

variable {F : Type*} [Field F]

def total (g : Gametes F) : F := g.x11 + g.x12 + g.x21 + g.x22

def pA (g : Gametes F) : F := g.x11 + g.x12

def pB (g : Gametes F) : F := g.x11 + g.x21

def pA' (g : Gametes F) : F := g.x21 + g.x22

def pB' (g : Gametes F) : F := g.x12 + g.x22

def D (g : Gametes F) : F := g.x11 * g.x22 - g.x12 * g.x21

def recombine (r : F) (g : Gametes F) : Gametes F where
  x11 := (1 - r) * g.x11 + r * g.pA * g.pB
  x12 := (1 - r) * g.x12 + r * g.pA * g.pB'
  x21 := (1 - r) * g.x21 + r * g.pA' * g.pB
  x22 := (1 - r) * g.x22 + r * g.pA' * g.pB'

theorem pA'_eq {g : Gametes F} (h : g.total = 1) : g.pA' = 1 - g.pA := by
  simp only [total, pA', pA] at *; linear_combination h

theorem pB'_eq {g : Gametes F} (h : g.total = 1) : g.pB' = 1 - g.pB := by
  simp only [total, pB', pB] at *; linear_combination h

/-- Source: lewontin_kojima1960, eq. (2), p. 459; lewontin1964, p. 50. -/
theorem D_eq_x11_sub {g : Gametes F} (h : g.total = 1) : g.D = g.x11 - g.pA * g.pB := by
  have h1 : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    simp only [total] at h; linear_combination h
  simp only [D, pA, pB, h1]; ring

theorem total_recombine {g : Gametes F} (r : F) (h : g.total = 1) :
    (recombine r g).total = 1 := by
  have h1 : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    simp only [total] at h; linear_combination h
  simp only [total, recombine, pA, pB, pA', pB', h1]; ring

theorem recombine_pA {g : Gametes F} (r : F) (h : g.total = 1) :
    (recombine r g).pA = g.pA := by
  have h1 : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    simp only [total] at h; linear_combination h
  simp only [pA, recombine, pB, pA', pB', h1]; ring

theorem recombine_pB {g : Gametes F} (r : F) (h : g.total = 1) :
    (recombine r g).pB = g.pB := by
  have h1 : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    simp only [total] at h; linear_combination h
  simp only [pB, recombine, pA, pA', pB', h1]; ring

/-- Source: robbins1918, eq. (5), p. 377; lewontin_kojima1960, eq. (3), p. 459; lewontin1964, p. 50.
-/
theorem D_recombine {g : Gametes F} (r : F) (h : g.total = 1) :
    (recombine r g).D = (1 - r) * g.D := by
  have h1 : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    simp only [total] at h; linear_combination h
  simp only [D, recombine, pA, pB, pA', pB', h1]; ring

/-- Source: robbins1918, eq. (5), p. 377; lewontin_kojima1960, eq. (3), p. 459; lewontin1964, p. 50.
-/
theorem D_iterate {g : Gametes F} (r : F) (h : g.total = 1) (t : ℕ) :
    ((recombine r)^[t] g).D = (1 - r) ^ t * g.D := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hn : ((recombine r)^[n] g).total = 1 := by
      clear ih
      induction n with
      | zero => simpa using h
      | succ m ihm => rw [Function.iterate_succ_apply']; exact total_recombine r ihm
    rw [Function.iterate_succ_apply', D_recombine r hn, ih]; ring

theorem iterate_pA_pB {g : Gametes F} (r : F) (h : g.total = 1) (t : ℕ) :
    ((recombine r)^[t] g).pA = g.pA ∧ ((recombine r)^[t] g).pB = g.pB ∧
      ((recombine r)^[t] g).total = 1 := by
  induction t with
  | zero => exact ⟨rfl, rfl, h⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    exact ⟨(recombine_pA r h3).trans h1, (recombine_pB r h3).trans h2, total_recombine r h3⟩

theorem recombine_nonneg [LinearOrder F] [IsStrictOrderedRing F] {g : Gametes F} {r : F}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (h11 : 0 ≤ g.x11) (h12 : 0 ≤ g.x12) (h21 : 0 ≤ g.x21)
    (h22 : 0 ≤ g.x22) :
    0 ≤ (recombine r g).x11 ∧ 0 ≤ (recombine r g).x12 ∧ 0 ≤ (recombine r g).x21 ∧
      0 ≤ (recombine r g).x22 := by
  have hs : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  simp only [recombine, pA, pB, pA', pB']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> positivity

end Gametes

end Rhone.Dynamics
