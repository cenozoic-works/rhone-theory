/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Exist

/-! # Non-vacuity: the one-allele model -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

variable {F : Type*} [Field F] {θA θB ρ : F}

private theorem mul_pred_add (a : ℕ) : a * (a - 1) + a = a * a := by
  cases a with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

private theorem nat_coal_id (x y : ℕ) : x * (x - 1 + 2 * y) + x = x * x + 2 * (x * y) := by
  cases x with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; ring

theorem nat_diag_id (a b c : ℕ) :
    (a + b + c) * ((a + b + c) - 1)
      = a * (a - 1 + 2 * c) + b * (b - 1 + 2 * c) + c * (c - 1) + 2 * (a * b) := by
  refine Nat.add_right_cancel (m := a + b + c) ?_
  calc (a + b + c) * ((a + b + c) - 1) + (a + b + c)
      = (a + b + c) * (a + b + c) := mul_pred_add _
    _ = (a * (a - 1 + 2 * c) + a) + (b * (b - 1 + 2 * c) + b) + (c * (c - 1) + c)
          + 2 * (a * b) := by
        rw [nat_coal_id, nat_coal_id, mul_pred_add]; ring
    _ = a * (a - 1 + 2 * c) + b * (b - 1 + 2 * c) + c * (c - 1) + 2 * (a * b)
          + (a + b + c) := by ring

theorem isSolution_one :
    IsSolution θA θB ρ (fun _ : Fin 1 => (1 : F)) (fun _ : Fin 1 => (1 : F))
      (fun _ : Config 1 1 => (1 : F)) := by
  refine ⟨rfl, fun i => rfl, fun j => rfl, fun i j => (one_mul 1).symm, ?_⟩
  intro ξ _
  have ha : ξ.sumA = ξ.a 0 := by simp [Config.sumA]
  have hb : ξ.sumB = ξ.b 0 := by simp [Config.sumB]
  have ht : ξ.t = ξ.c 0 0 := by simp [Config.t]
  have hrow : ξ.cRow 0 = ξ.c 0 0 := by simp [Config.cRow]
  have hcol : ξ.cCol 0 = ξ.c 0 0 := by simp [Config.cCol]
  simp only [diag, rhs, Config.coalA, Config.coalB, Config.coalC, Config.coalAB,
    Config.n, Config.nA, Config.nB, ha, hb, ht, hrow, hcol, Fin.sum_univ_one, mul_one, one_mul]
  rw [nat_diag_id]
  push_cast
  ring

theorem q_eq_one [LinearOrder F] [IsStrictOrderedRing F] (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) :
    q (πA := fun _ : Fin 1 => (1 : F)) (πB := fun _ : Fin 1 => (1 : F)) hθA hθB hρ
      = fun _ : Config 1 1 => (1 : F) :=
  (q_unique hθA hθB hρ isSolution_one).symm

end Rhone.LinearAlgebra.Recursion
