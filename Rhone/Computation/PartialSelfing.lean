/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Absorption
public import Init.Data.List.OfFn
public import Init.Data.Nat.Mod

/-! # Init-only rational fair-transmission laws and complete local certificates -/

@[expose] public section
namespace Rhone.Computation.PartialSelfing

abbrev Diploid (d : Nat) := Fin 2 → Fin d

def pair {d : Nat} (a b : Fin d) : Diploid d := fun i => if i = 0 then a else b

def sumFin (n : Nat) (f : Fin n → Rat) : Rat :=
  Absorption.sum (fun i => if h : i < n then f ⟨i, h⟩ else 0) n

def sumDip (d : Nat) (f : Diploid d → Rat) : Rat :=
  sumFin d (fun a => sumFin d (fun b => f (pair a b)))

def sumParents (d : Nat) (f : Diploid d × Diploid d → Rat) : Rat :=
  sumDip d (fun x => sumDip d (fun y => f (x, y)))

def transmission {d : Nat} (w : Rat) (x y z : Diploid d) : Rat :=
  sumFin 2 (fun i => sumFin 2 (fun j =>
    if x i = z 0 ∧ y j = z 1 then w / 4 else 0))

def selfed {d : Nat} (p : Diploid d → Rat) (z : Diploid d) : Rat :=
  sumDip d (fun x => transmission (p x) x x z)

def outcross {d : Nat} (q : Diploid d × Diploid d → Rat) (z : Diploid d) : Rat :=
  sumParents d (fun xy => transmission (q xy) xy.1 xy.2 z)

def step {d : Nat} (s : Rat) (q : Diploid d × Diploid d → Rat)
    (p : Diploid d → Rat) (z : Diploid d) : Rat :=
  s * selfed p z + (1 - s) * outcross q z

def generation {d : Nat} (s : Rat) (q : Diploid d × Diploid d → Rat)
    (p : Diploid d → Rat) : Nat → Diploid d → Rat
  | 0 => p
  | t + 1 => step s q (generation s q p t)

def ibd {d : Nat} (p : Diploid d → Rat) : Rat :=
  sumDip d (fun x => p x * if x 0 = x 1 then 1 else 0)

def kinship {d : Nat} (q : Diploid d × Diploid d → Rat) : Rat :=
  sumParents d (fun xy => q xy * sumFin 2 (fun i => sumFin 2 (fun j =>
    (if xy.1 i = xy.2 j then 1 else 0) / 4)))

def fixed (s : Rat) : Rat := s / (2 - s)

def dipIndex {d : Nat} (x : Diploid d) : Nat := (x 0).val * d + (x 1).val

def parentIndex {d : Nat} (xy : Diploid d × Diploid d) : Nat :=
  dipIndex xy.1 * (d * d) + dipIndex xy.2

def dipLaw (d : Nat) (p : Array Rat) : Diploid d → Rat := fun x => p.getD (dipIndex x) 0

def parentLaw (d : Nat) (q : Array Rat) : Diploid d × Diploid d → Rat :=
  fun xy => q.getD (parentIndex xy) 0

def decode {d : Nat} (i : Fin (d * d)) : Fin d × Fin d :=
  (⟨i.val / d, Nat.div_lt_of_lt_mul i.isLt⟩,
    ⟨i.val % d, Nat.mod_lt _ (Nat.pos_of_mul_pos_left
      (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))⟩)

def lawArray (d : Nat) (p : Diploid d → Rat) : Array Rat :=
  Array.ofFn (fun i : Fin (d * d) => p (pair (decode i).1 (decode i).2))

def rowStep (d : Nat) (s : Rat) (environment previous : Array Rat) : Array Rat :=
  lawArray d (fun z => s * selfed (dipLaw d previous) z +
    (1 - s) * dipLaw d environment z)

def rows (d : Nat) (s : Rat) (q p : Array Rat) (t : Nat) : Array (Array Rat) := Id.run do
  let environment := lawArray d (outcross (parentLaw d q))
  let mut answer := #[p]
  let mut previous := p
  for _ in List.range t do
    previous := rowStep d s environment previous
    answer := answer.push previous
  return answer

abbrev ValidInput (d t : Nat) (s : Rat) (q p : Array Rat) : Prop :=
  2 ≤ d ∧ d ≤ 8 ∧ t ≤ 128 ∧ 0 ≤ s ∧ s ≤ 1 ∧
  p.size = d * d ∧ q.size = (d * d) * (d * d) ∧
  (∀ a b : Fin d, 0 ≤ dipLaw d p (pair a b)) ∧
  (∀ a b c e : Fin d, 0 ≤ parentLaw d q (pair a b, pair c e)) ∧
  sumDip d (dipLaw d p) = 1 ∧ sumParents d (parentLaw d q) = 1 ∧
  kinship (parentLaw d q) = 0

abbrev ValidCertificate (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat) : Prop :=
  ValidInput d t s q p ∧ environment.size = d * d ∧
  (∀ a b : Fin d, dipLaw d environment (pair a b) = outcross (parentLaw d q) (pair a b)) ∧
  table.size = t + 1 ∧ moments.size = t + 1 ∧ table.getD 0 #[] = p ∧
  (∀ k : Fin (t + 1), (table.getD k #[]).size = d * d ∧
    moments.getD k 0 = ibd (dipLaw d (table.getD k #[]))) ∧
  (∀ k : Fin t, ∀ a b : Fin d,
    dipLaw d (table.getD (k.val + 1) #[]) (pair a b) =
      s * selfed (dipLaw d (table.getD k #[])) (pair a b) +
      (1 - s) * dipLaw d environment (pair a b)) ∧
  equilibrium = fixed s ∧ qKinship = kinship (parentLaw d q)

def check (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat) : Bool :=
  decide (ValidCertificate d t s q p environment table moments equilibrium qKinship)

end Rhone.Computation.PartialSelfing
