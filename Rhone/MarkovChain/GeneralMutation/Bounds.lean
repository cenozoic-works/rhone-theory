/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Weight

/-! # Weighted absolute-value estimates used by the general-mutation uniqueness proof -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

theorem nat_degenerate {u v t : ℕ} (h2 : 2 ≤ u + v + t)
    (heq : 2 * (u * v) = (u + v + t) * (u + v + t - 1)) : t = 0 ∧ u = 1 ∧ v = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, u + v + t = m + 2 := ⟨u + v + t - 2, by omega⟩
  have h1 : u + v + t - 1 = m + 1 := by omega
  rw [h1, hm] at heq
  have hz : (2 : ℤ) * ((u : ℤ) * (v : ℤ)) = ((m : ℤ) + 2) * ((m : ℤ) + 1) := by
    exact_mod_cast heq
  have hs : (u : ℤ) + (v : ℤ) + (t : ℤ) = (m : ℤ) + 2 := by exact_mod_cast hm
  have hmz : m = 0 := by
    have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have huv : (0 : ℤ) ≤ (u : ℤ) + (v : ℤ) := by positivity
    have hle : (m : ℤ) ≤ 0 := by
      nlinarith [sq_nonneg ((u : ℤ) - (v : ℤ)), mul_nonneg ht huv]
    omega
  rw [hmz] at heq hm
  have hu2 : u ≤ 2 := by omega
  have hv2 : v ≤ 2 := by omega
  interval_cases u <;> interval_cases v <;> omega

def cab (ξ : Config KA KB) : ℕ :=
  if 2 * (ξ.sumA * ξ.sumB) < ξ.n * (ξ.n - 1) then 2 * (ξ.sumA * ξ.sumB) else 0

theorem cab_lt (ξ : Config KA KB) (hn : 2 ≤ ξ.n) : cab ξ < ξ.n * (ξ.n - 1) := by
  rw [cab]
  split_ifs with hlt
  · exact hlt
  · obtain ⟨m, hm⟩ : ∃ m, ξ.n = m + 2 := ⟨ξ.n - 2, by omega⟩
    have h1 : ξ.n - 1 = m + 1 := by omega
    rw [h1, hm]
    positivity

theorem mut_line_bound {ι : Type*} [Fintype ι] {ν : ι → F} {P : ι → ι → F}
    (hP : ∀ k i, 0 ≤ P k i) (hν : ∀ i, 0 < ν i) (hst : ∀ i, ∑ k, ν k * P k i = ν i)
    {g : ι → F} {M W : F} (i : ι)
    (hg : ∀ k, |g k| * ν i ≤ M * (W * ν k)) :
    ∑ k, P k i * |g k| ≤ M * W := by
  have key : (∑ k, P k i * |g k|) * ν i ≤ (M * W) * ν i := by
    calc (∑ k, P k i * |g k|) * ν i = ∑ k, P k i * (|g k| * ν i) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ k, P k i * (M * (W * ν k)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hg k) (hP k i)
      _ = (M * W) * ∑ k, ν k * P k i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = (M * W) * ν i := by rw [hst i]
  exact le_of_mul_le_mul_right key (hν i)

theorem mut_cell_bound {ι : Type*} [Fintype ι] {ν : ι → F} {P : ι → ι → F}
    (hP : ∀ k i, 0 ≤ P k i) (hν : ∀ i, 0 < ν i) (hst : ∀ i, ∑ k, ν k * P k i = ν i)
    {M W : F} (i : ι) (w : ℕ) {g : ι → F}
    (hg : w ≠ 0 → ∀ k, |g k| * ν i ≤ M * (W * ν k)) :
    |∑ k, P k i * ((w : ℕ) : F) * g k| ≤ ((w : ℕ) : F) * (M * W) := by
  by_cases hw : w = 0
  · simp [hw]
  have hinner : ∑ k, P k i * |g k| ≤ M * W := mut_line_bound hP hν hst i (hg hw)
  calc |∑ k, P k i * ((w : ℕ) : F) * g k|
      ≤ ∑ k, |P k i * ((w : ℕ) : F) * g k| := Finset.abs_sum_le_sum_abs _ _
    _ = ((w : ℕ) : F) * ∑ k, P k i * |g k| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hP k i), abs_of_nonneg (Nat.cast_nonneg _)]
        ring
    _ ≤ ((w : ℕ) : F) * (M * W) := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)

end Rhone.MarkovChain.GeneralMutation
