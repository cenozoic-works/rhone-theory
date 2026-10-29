/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GelfandTsetlinEdges.Basic

/-! # The sector law on a tabulated edge, as an integer predicate -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

structure Edge where
  blk : ℕ × ℕ
  lam : List ℕ
  mu : List ℕ
  nu : List ℕ
  r : ℕ
  R : ℕ
  pn : ℤ
  pd : ℕ
  open58 : Bool

def betaAt (p : List ℕ) (R s : ℕ) : ℤ := (p.getD s 0 : ℤ) + (R : ℤ) - 1 - (s : ℤ)

def numerAt (e : Edge) (R : ℕ) : ℤ :=
  (betaAt e.nu R e.r + 1)
    * ((List.range R).map fun s => betaAt e.lam R s - betaAt e.nu R e.r).prod
    * ((List.range R).map fun s => betaAt e.mu R s - betaAt e.nu R e.r).prod

def denomAt (e : Edge) (R : ℕ) : ℤ :=
  ((List.range R).map fun s =>
    if s = e.r then 1
    else (betaAt e.nu R s - betaAt e.nu R e.r) * (betaAt e.nu R s - betaAt e.nu R e.r - 1)).prod

def edgeOKat (e : Edge) (R : ℕ) : Bool :=
  denomAt e R != 0 && e.pd != 0 && e.pn * denomAt e R == numerAt e R * (e.pd : ℤ)

def edgeOK (e : Edge) : Bool := (List.range 3).all fun d => edgeOKat e (e.R + d)

def measured (e : Edge) : ℚ := (e.pn : ℚ) / (e.pd : ℚ)

def lawAt (e : Edge) (R : ℕ) : ℚ := (numerAt e R : ℚ) / (denomAt e R : ℚ)

def bQ (p : List ℕ) (R : ℕ) : Fin R → ℚ := fun s => (betaAt p R s : ℚ)

end Rhone.LinearAlgebra.GelfandTsetlinEdges
