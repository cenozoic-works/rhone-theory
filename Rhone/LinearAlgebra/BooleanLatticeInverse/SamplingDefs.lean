/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.BlockInverse
public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Definitions for the explicit sampling probability with a biallelic `B` locus -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Recursion

variable {KA : ℕ} {F : Type*} [Field F]

def pull {n : ℕ} (x : Fin (n + 1)) (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun y => x.succAbove y ∈ S

def kapA (πA : Fin KA → F) (p p' : Fin KA) : F :=
  (if p = p' then πA p else 0) - πA p * πA p'

def kapB (πB : Fin 2 → F) : F := πB 0 * πB 1

def gamB (πB : Fin 2 → F) : F := πB 1 - πB 0

abbrev Tab (KA : ℕ) (F : Type*) : Type _ :=
  (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F

section Source

variable (πA : Fin KA → F) (πB : Fin 2 → F) (P : Tab KA F)

def aTerm : (n : ℕ) → (Fin n → Fin KA) → Fin KA → ℕ → Finset (Fin n) → Fin n → F
  | 0, _, _, _, _, _ => 0
  | n + 1, lab, p', j, S, z =>
    kapA πA (lab z) p' * P n (lab ∘ z.succAbove) j (pull z S)
      + ((if lab z = p' then 1 else 0) - πA p') * P (n + 1) lab j S
      - πA (lab z) * P (n + 1) (Function.update lab z p') j S

def pairSrc : (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F
  | 0, _, _, _ => 0
  | n + 1, lab, j, S =>
    ∑ x' : Fin (n + 1), ∑ z : Fin n,
      if x' ∈ S then
        if z ∈ pull x' S then
          kapB πB * aTerm πA P n (lab ∘ x'.succAbove) (lab x') (j - 2) ((pull x' S).erase z) z
            + gamB πB * aTerm πA P n (lab ∘ x'.succAbove) (lab x') (j - 1) (pull x' S) z
        else 0
      else
        (if z ∈ pull x' S then 2 else 1)
          * aTerm πA P n (lab ∘ x'.succAbove) (lab x') j (pull x' S) z

def srcKB2 (n : ℕ) (lab : Fin n → Fin KA) (j : ℕ) (S : Finset (Fin n)) : F :=
  pairSrc πA πB P n lab j S
    + (((j - S.card) * (j - S.card - 1) : ℕ) : F)
      * (kapB πB * P n lab (j - 2) S + gamB πB * P n lab (j - 1) S)
    + 2 * ((j - S.card : ℕ) : F)
      * ∑ x ∈ S, (kapB πB * P n lab (j - 2) (S.erase x) + gamB πB * P n lab (j - 1) S)

end Source

def PhiTab (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) : ℕ → Tab KA F
  | 0, _, _, _, _ => 1
  | f + 1, n, lab, j, S =>
    if n + j = 0 then 1
    else blockSol θA θB ρ j (srcKB2 πA πB (PhiTab θA θB ρ πA πB f) n lab j) S

def PhiX (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) : Tab KA F :=
  fun n lab j S => PhiTab θA θB ρ πA πB (n + j) n lab j S

inductive Slot (KA : ℕ) : Type
  | freeA (p : Fin KA)
  | freeB (b : Fin 2)
  | pair (p : Fin KA) (b : Fin 2)

def slots (ξ : Config KA 2) : List (Slot KA) :=
  ((List.finRange KA).flatMap fun p => List.replicate (ξ.a p) (Slot.freeA p))
    ++ ((List.finRange 2).flatMap fun b => List.replicate (ξ.b b) (Slot.freeB b))
    ++ ((List.finRange KA).flatMap fun p => (List.finRange 2).flatMap fun b =>
      List.replicate (ξ.c p b) (Slot.pair p b))

def sgnB (b : Fin 2) : F := if b = 0 then 1 else -1

def asm (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) :
    List (Slot KA) → (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F
  | [], n, lab, j, S => PhiX θA θB ρ πA πB n lab j S
  | Slot.freeA p :: r, n, lab, j, S =>
    πA p * asm θA θB ρ πA πB r n lab j S
      + asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) j
        (S.map (Fin.succEmb n))
  | Slot.freeB b :: r, n, lab, j, S =>
    πB b * asm θA θB ρ πA πB r n lab j S + sgnB b * asm θA θB ρ πA πB r n lab (j + 1) S
  | Slot.pair p b :: r, n, lab, j, S =>
    πA p * πB b * asm θA θB ρ πA πB r n lab j S
      + πB b * asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) j
        (S.map (Fin.succEmb n))
      + πA p * sgnB b * asm θA θB ρ πA πB r n lab (j + 1) S
      + sgnB b * asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) (j + 1)
        (insert 0 (S.map (Fin.succEmb n)))

def qExplicitKB2 (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) (ξ : Config KA 2) : F :=
  asm θA θB ρ πA πB (slots ξ) 0 Fin.elim0 0 ∅

end Rhone.LinearAlgebra.BooleanLatticeInverse
