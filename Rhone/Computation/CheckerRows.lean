/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy

/-! # Exact table construction with duplicate rejection -/

@[expose] public section
namespace Rhone.Computation

def checkerRowValid (n : Nat) (s : Config) : Bool :=
  s.a.size == 2 && s.b.size == 2 && s.c.size == 4 &&
    s.block.1 ≤ n && s.block.2 ≤ n

def insertTableRows (n : Nat) : List (Config × Rat) → Std.HashMap String Rat →
    Option (Std.HashMap String Rat)
  | [], table => some table
  | (s, v) :: rows, table =>
    if checkerRowValid n s && !table.contains s.key then
      insertTableRows n rows (table.insert s.key v)
    else none

end Rhone.Computation
