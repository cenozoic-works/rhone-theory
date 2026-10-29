/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerRecursion
public import Rhone.Computation.CheckerMovesProof

/-! # Exact finite-sum recursion bridge -/

@[expose] public section

namespace Rhone.Computation.CheckerEncoding

open LinearAlgebra.Recursion

@[simp] theorem decrementCounts_eq (xs : Array Nat) (i : Nat) :
    decrementCounts xs i = decrement xs i := rfl

@[simp] theorem incrementCounts_eq (xs : Array Nat) (i : Nat) :
    incrementCounts xs i = increment xs i := rfl

theorem recursionRhsDirect_encode (p : Params) (value : Rhone.Computation.Config → Rat)
    (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    recursionRhsDirect p value (encode ξ) =
      rhs p.thetaA p.thetaB p.rho (fun i => p.piA.getD i.val 0)
        (fun j => p.piB.getD j.val 0) (fun η => value (encode η)) ξ := by
  simp only [rhs, Fin.sum_univ_two, Config.coalA, Config.coalB, Config.coalC,
    Config.coalAB, Config.cRow, Config.cCol, recursionRhsDirect,
    decrementCounts_eq, incrementCounts_eq, encode_dropA, encode_dropB,
    encode_dropC, encode_mergeAB, encode_killA, encode_killB, encode_split]
  simp [encode]
  ring

end Rhone.Computation.CheckerEncoding
