/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Field-algebra core of the Gelfand–Tsetlin edge law: definitions -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

open Finset

variable {F : Type*} [Field F] {n : ℕ}

def Glaw (x z : Fin (n + 1) → F) (r : Fin (n + 1)) : F :=
  (∏ s, (x s - z r)) / ∏ s ∈ univ.erase r, (z s - z r)

def Aup (x z : Fin (n + 1) → F) (r : Fin (n + 1)) : F :=
  -((∏ s, (x s - z r)) * (-1 - z r)) / ∏ s ∈ univ.erase r, (z s - z r)

def Adown (z : Fin (n + 1) → F) (r : Fin (n + 1)) : F :=
  (∏ j : Fin n, (z j.castSucc - z r - 1)) / ∏ s ∈ univ.erase r, (z s - z r - 1)

def cBeta (z : Fin (n + 1) → F) (r : Fin (n + 1)) : F :=
  (z r + 1) * ∏ s ∈ univ.erase r, ((z s - z r) / (z s - z r - 1))

def sectorLaw (x y z : Fin (n + 1) → F) (r : Fin (n + 1)) : F :=
  ((z r + 1) * ∏ s, ((x s - z r) * (y s - z r))) /
    ∏ s ∈ univ.erase r, ((z s - z r) * (z s - z r - 1))

def eAdd (z : Fin (n + 1) → F) (r : Fin (n + 1)) : Fin (n + 1) → F :=
  Function.update z r (z r + 1)

def bMu0 (z : Fin (n + 1) → F) (ε : F) : Fin (n + 1) → F :=
  Fin.cons (z 0 + ε) fun j : Fin n => z j.castSucc - 1

def offSum (F : Type*) [Field F] (n : ℕ) : F := ∑ s : Fin (n + 1), ((n : F) - ((s : ℕ) : F))

def offSqSum (F : Type*) [Field F] (n : ℕ) : F :=
  ∑ s : Fin (n + 1), ((n : F) - ((s : ℕ) : F)) ^ 2

def sizeB (b : Fin (n + 1) → F) : F := ∑ s, (b s - ((n : F) - ((s : ℕ) : F)))

def CB (b : Fin (n + 1) → F) : F :=
  (∑ s, b s ^ 2) - (2 * (n : F) + 1) * sizeB b - offSqSum F n

def mB (bl bm bn : Fin (n + 1) → F) : F := sizeB bl + sizeB bm - 2 * sizeB bn

def kappaB (bl bm bn : Fin (n + 1) → F) : F :=
  mB bl bm bn * (mB bl bm bn - 1) / 2 - sizeB bn + CB bn - (CB bl + CB bm) / 2

end Rhone.LinearAlgebra.GelfandTsetlinEdges
