/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable kinship and inbreeding on a finite pedigree

Source: malecot1969, ch. 1, pp. 8–10; felsenstein_teg2019, pp. 226–227, eq. (V-13)–(V-18). -/

@[expose] public section
namespace Rhone.Computation.Kinship

abbrev Ped := List (Option (Nat × Nat))

def parents (ped : Ped) (i : Nat) : Option (Nat × Nat) := (ped[i]?).getD none

def kinshipF (ped : Ped) : Nat → Nat → Nat → Rat
  | 0, _, _ => 0
  | f + 1, i, j =>
    if i = j then
      match parents ped i with
      | none => 1 / 2
      | some (a, b) => (1 + kinshipF ped f a b) / 2
    else if i < j then
      match parents ped j with
      | none => 0
      | some (a, b) => (kinshipF ped f i a + kinshipF ped f i b) / 2
    else
      match parents ped i with
      | none => 0
      | some (a, b) => (kinshipF ped f a j + kinshipF ped f b j) / 2

def kinship (ped : Ped) (i j : Nat) : Rat := kinshipF ped (i + j + 1) i j

def inbreeding (ped : Ped) (i : Nat) : Rat :=
  match parents ped i with
  | none => 0
  | some (a, b) => kinship ped a b

def kinshipMatrix (ped : Ped) (n : Nat) : List (List Rat) :=
  (List.range n).map fun i => (List.range n).map fun j => kinship ped i j

end Rhone.Computation.Kinship
