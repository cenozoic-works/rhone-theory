/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Closure
public import Mathlib.Data.List.Range

/-! # Membership in the complete finite closure -/

@[expose] public section
namespace Rhone.Computation

theorem configOfCounts_inj {a0 a1 b0 b1 c00 c01 c10 c11 : Nat}
    {a0' a1' b0' b1' c00' c01' c10' c11' : Nat} :
    configOfCounts a0 a1 b0 b1 c00 c01 c10 c11 =
      configOfCounts a0' a1' b0' b1' c00' c01' c10' c11' ↔
    a0 = a0' ∧ a1 = a1' ∧ b0 = b0' ∧ b1 = b1' ∧
      c00 = c00' ∧ c01 = c01' ∧ c10 = c10' ∧ c11 = c11' := by
  simp [configOfCounts, Config.mk.injEq, Array.mk.injEq, and_assoc]

theorem configOfCounts_mem_closure {n a0 a1 b0 b1 c00 c01 c10 c11 : Nat} :
    configOfCounts a0 a1 b0 b1 c00 c01 c10 c11 ∈ closure n ↔
    a0 + a1 + (c00 + c01 + c10 + c11) ≤ n ∧
      b0 + b1 + (c00 + c01 + c10 + c11) ≤ n := by
  simp only [closure, List.mem_toArray, closureList, List.mem_flatMap, List.mem_range,
    List.mem_map, configOfCounts_inj]
  constructor
  · rintro ⟨x00, h00, x01, h01, x10, h10, x11, h11,
      xa0, ha0, xa1, ha1, xb0, hb0, xb1, hb1,
      ea0, ea1, eb0, eb1, e00, e01, e10, e11⟩
    subst xa0 xa1 xb0 xb1 x00 x01 x10 x11
    omega
  · intro h
    refine ⟨c00, by omega, c01, by omega, c10, by omega, c11, by omega,
      a0, by omega, a1, by omega, b0, by omega, b1, by omega,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Rhone.Computation
