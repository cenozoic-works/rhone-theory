/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Sfs
public import Init.Data.List.OfFn

/-!
# Exact summaries of unfolded observed counts

Source: watterson1975, sec. 1.2, p. 257; durrett2008, Thm 1.22; tajima1989, p. 586, eq. (10)–(12);
fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Computation.SfsObserved

def total (counts : Array Nat) : Nat :=
  (List.ofFn (fun k : Fin counts.size => counts[k.val])).sum

def pairWeight (n i : Nat) : Rat :=
  (i : Rat) * ((n - i : Nat) : Rat) /
    ((n : Rat) * ((n - 1 : Nat) : Rat) / 2)

def pairwise (n : Nat) (counts : Array Nat) : Rat :=
  (List.ofFn (fun k : Fin counts.size =>
    pairWeight n (k.val + 1) * (counts[k.val] : Rat))).sum

def values (n : Nat) (counts : Array Nat) : Array Rat :=
  #[((total counts : Nat) : Rat), Sfs.watterson n (total counts), pairwise n counts]

end Rhone.Computation.SfsObserved
