/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Config

/-! # Complete biallelic marginal closure -/

@[expose] public section
namespace Rhone.Computation

def configOfCounts (a0 a1 b0 b1 c00 c01 c10 c11 : Nat) : Config :=
  ⟨#[a0, a1], #[b0, b1], #[c00, c01, c10, c11]⟩

def closureList (n : Nat) : List Config :=
  (List.range (n + 1)).flatMap fun c00 =>
    (List.range (n - c00 + 1)).flatMap fun c01 =>
      (List.range (n - c00 - c01 + 1)).flatMap fun c10 =>
        (List.range (n - c00 - c01 - c10 + 1)).flatMap fun c11 =>
          let linked := c00 + c01 + c10 + c11
          (List.range (n - linked + 1)).flatMap fun a0 =>
            (List.range (n - linked - a0 + 1)).flatMap fun a1 =>
              (List.range (n - linked + 1)).flatMap fun b0 =>
                (List.range (n - linked - b0 + 1)).map fun b1 =>
                  configOfCounts a0 a1 b0 b1 c00 c01 c10 c11

def closure (n : Nat) : Array Config := (closureList n).toArray

end Rhone.Computation
