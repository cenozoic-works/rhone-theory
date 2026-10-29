/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Config

/-! # The bookkeeping identities -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

namespace Config

variable {KA KB : ℕ}

private theorem mul_pred_add (a : ℕ) : a * (a - 1) + a = a * a := by
  cases a with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

theorem bookkeeping_diag (ξ : Config KA KB) :
    ξ.n * (ξ.n - 1) + ξ.t * (ξ.t - 1)
      = ξ.nA * (ξ.nA - 1) + ξ.nB * (ξ.nB - 1) + 2 * (ξ.sumA * ξ.sumB) := by
  refine Nat.add_right_cancel (m := ξ.n + ξ.t + ξ.nA + ξ.nB) ?_
  calc ξ.n * (ξ.n - 1) + ξ.t * (ξ.t - 1) + (ξ.n + ξ.t + ξ.nA + ξ.nB)
      = (ξ.n * (ξ.n - 1) + ξ.n) + (ξ.t * (ξ.t - 1) + ξ.t) + ξ.nA + ξ.nB := by ring
    _ = ξ.n * ξ.n + ξ.t * ξ.t + ξ.nA + ξ.nB := by
        rw [mul_pred_add, mul_pred_add]
    _ = ξ.nA * ξ.nA + ξ.nB * ξ.nB + 2 * (ξ.sumA * ξ.sumB) + ξ.n + ξ.t := by
        simp only [n, nA, nB]; ring
    _ = (ξ.nA * (ξ.nA - 1) + ξ.nA) + (ξ.nB * (ξ.nB - 1) + ξ.nB)
          + 2 * (ξ.sumA * ξ.sumB) + ξ.n + ξ.t := by
        rw [mul_pred_add, mul_pred_add]
    _ = ξ.nA * (ξ.nA - 1) + ξ.nB * (ξ.nB - 1) + 2 * (ξ.sumA * ξ.sumB)
          + (ξ.n + ξ.t + ξ.nA + ξ.nB) := by ring

theorem bookkeeping_coalA (ξ : Config KA KB) (i : Fin KA) :
    ξ.a i * (ξ.a i - 1 + 2 * ξ.cRow i) + ξ.cRow i * (ξ.cRow i - 1)
      = ξ.mA i * (ξ.mA i - 1) := by
  simp only [mA]
  rcases Nat.eq_zero_or_pos (ξ.a i) with h | h
  · rw [h]; simp
  rcases Nat.eq_zero_or_pos (ξ.cRow i) with h' | h'
  · rw [h']; simp
  obtain ⟨p, hp⟩ : ∃ p, ξ.a i = p + 1 := ⟨ξ.a i - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, ξ.cRow i = s + 1 := ⟨ξ.cRow i - 1, by omega⟩
  rw [hp, hs]
  have e1 : p + 1 - 1 = p := by omega
  have e2 : s + 1 - 1 = s := by omega
  have e3 : p + 1 + (s + 1) - 1 = p + s + 1 := by omega
  rw [e1, e2, e3]
  ring

theorem bookkeeping_coalB (ξ : Config KA KB) (j : Fin KB) :
    ξ.b j * (ξ.b j - 1 + 2 * ξ.cCol j) + ξ.cCol j * (ξ.cCol j - 1)
      = ξ.mB j * (ξ.mB j - 1) := by
  simp only [mB]
  rcases Nat.eq_zero_or_pos (ξ.b j) with h | h
  · rw [h]; simp
  rcases Nat.eq_zero_or_pos (ξ.cCol j) with h' | h'
  · rw [h']; simp
  obtain ⟨p, hp⟩ : ∃ p, ξ.b j = p + 1 := ⟨ξ.b j - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, ξ.cCol j = s + 1 := ⟨ξ.cCol j - 1, by omega⟩
  rw [hp, hs]
  have e1 : p + 1 - 1 = p := by omega
  have e2 : s + 1 - 1 = s := by omega
  have e3 : p + 1 + (s + 1) - 1 = p + s + 1 := by omega
  rw [e1, e2, e3]
  ring

end Config

end Rhone.LinearAlgebra.Recursion
