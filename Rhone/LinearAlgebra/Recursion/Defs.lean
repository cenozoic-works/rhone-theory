/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Config

/-! # The killed-PIM two-locus recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]

namespace Config

def coalA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.a i * (ξ.a i - 1 + 2 * ξ.cRow i)

def coalB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.b j * (ξ.b j - 1 + 2 * ξ.cCol j)

def coalC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := ξ.c i j * (ξ.c i j - 1)

def coalAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := 2 * (ξ.a i * ξ.b j)

theorem coalA_eq_zero_of (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i = 0) : ξ.coalA i = 0 := by
  simp [coalA, h]

theorem coalB_eq_zero_of (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j = 0) : ξ.coalB j = 0 := by
  simp [coalB, h]

theorem coalC_eq_zero_of (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j = 0) :
    ξ.coalC i j = 0 := by
  simp [coalC, h]

theorem coalAB_eq_zero_left (ξ : Config KA KB) {i : Fin KA} (j : Fin KB) (h : ξ.a i = 0) :
    ξ.coalAB i j = 0 := by
  simp [coalAB, h]

theorem coalAB_eq_zero_right (ξ : Config KA KB) (i : Fin KA) {j : Fin KB} (h : ξ.b j = 0) :
    ξ.coalAB i j = 0 := by
  simp [coalAB, h]

end Config

def diag (θA θB ρ : F) (ξ : Config KA KB) : F :=
  ((ξ.n * (ξ.n - 1) : ℕ) : F) + θA * (ξ.nA : ℕ) + θB * (ξ.nB : ℕ) + ρ * (ξ.t : ℕ)

def rhs (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
    + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j))
    + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j))
    + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

structure IsSolution (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = πA i
  bdryB : ∀ j, q (Config.eB j) = πB j
  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n → diag θA θB ρ ξ * q ξ = rhs θA θB ρ πA πB q ξ

end Rhone.LinearAlgebra.Recursion
