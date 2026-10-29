/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Kernel

/-! # Level-free residual criterion at a root of the denominator polynomial -/

@[expose] public section

namespace Rhone.Analysis.DenominatorEquation

open Matrix LinearAlgebra.Tridiag RecombinationExpansion LinearAlgebra.RecombinationExpansion

section Divisibility

variable {A : Type*} [CommRing A] {n : ℕ}

theorem level_free {e : A} (he : Prime e) (Uu : Fin (n + 1) → Fin (n + 1) → A)
    (Rv : Fin (n + 1) → A) (t z : Fin (n + 1))
    (h0 : ¬ e ∣ Uu 0 z) (ht : ¬ e ∣ Uu t z)
    (hminor : ∀ s, e ∣ (Uu t s * Uu 0 z - Uu t z * Uu 0 s)) :
    (e ∣ ∑ s, Uu t s * Rv s) ↔ (e ∣ ∑ s, Uu 0 s * Rv s) := by
  have key : e ∣ Uu 0 z * (∑ s, Uu t s * Rv s) - Uu t z * (∑ s, Uu 0 s * Rv s) := by
    have hexp : Uu 0 z * (∑ s, Uu t s * Rv s) - Uu t z * (∑ s, Uu 0 s * Rv s)
        = ∑ s, (Uu t s * Uu 0 z - Uu t z * Uu 0 s) * Rv s := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hexp]
    exact Finset.dvd_sum fun s _ => Dvd.dvd.mul_right (hminor s) _
  constructor
  · intro hdvd
    have h1 : e ∣ Uu t z * (∑ s, Uu 0 s * Rv s) := by
      have h2 : Uu t z * (∑ s, Uu 0 s * Rv s)
          = Uu 0 z * (∑ s, Uu t s * Rv s)
            - (Uu 0 z * (∑ s, Uu t s * Rv s) - Uu t z * (∑ s, Uu 0 s * Rv s)) := by ring
      rw [h2]
      exact dvd_sub (Dvd.dvd.mul_left hdvd _) key
    exact (he.dvd_mul.mp h1).resolve_left ht
  · intro hdvd
    have h1 : e ∣ Uu 0 z * (∑ s, Uu t s * Rv s) := by
      have h2 : Uu 0 z * (∑ s, Uu t s * Rv s)
          = (Uu 0 z * (∑ s, Uu t s * Rv s) - Uu t z * (∑ s, Uu 0 s * Rv s))
            + Uu t z * (∑ s, Uu 0 s * Rv s) := by ring
      rw [h2]
      exact dvd_add key (Dvd.dvd.mul_left hdvd _)
    exact (he.dvd_mul.mp h1).resolve_left h0

end Divisibility

section AtRoot

variable {K : Type*} [Field K] [CharZero K]
variable (i j : ℕ) (θA θB ρ : K)

theorem adj_last_col_ne_zero (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (t : Fin (min i j + 1)) :
    U K i j θA θB ρ t (Fin.last (min i j)) ≠ 0 := by
  have ht : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  rw [U_apply, show ((Fin.last (min i j) : Fin (min i j + 1)) : ℕ) = min i j from rfl,
    adj_last_col i j θA θB ρ ht]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_)
    (Delta_ne_zero i j θA θB ρ hρ hE hcop (t : ℕ) ht)
  refine Finset.prod_ne_zero_iff.mpr fun u hu => ?_
  rw [Finset.mem_Ico] at hu
  refine Nat.cast_ne_zero.mpr (Nat.mul_ne_zero ?_ ?_)
  · have : u < i := lt_of_lt_of_le hu.2 (min_le_left i j)
    omega
  · have : u < j := lt_of_lt_of_le hu.2 (min_le_right i j)
    omega

theorem U_zero_zero_ne_zero (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0) :
    U K i j θA θB ρ 0 0 ≠ 0 := by
  rw [U_zero_apply, show ((0 : Fin (min i j + 1)) : ℕ) = 0 from rfl]
  exact ell_ne_zero i j θA θB ρ hρ hE hcop (Nat.zero_le _)

theorem level_free_at_root (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (Rv : Fin (min i j + 1) → K) (t : Fin (min i j + 1)) :
    (∑ s, U K i j θA θB ρ t s * Rv s) = 0 ↔ (∑ s, U K i j θA θB ρ 0 s * Rv s) = 0 := by
  have h00 : U K i j θA θB ρ 0 0 ≠ 0 := U_zero_zero_ne_zero i j θA θB ρ hρ hE hcop
  have h0m : U K i j θA θB ρ 0 (Fin.last (min i j)) ≠ 0 :=
    adj_last_col_ne_zero i j θA θB ρ hρ hE hcop 0
  have htm : U K i j θA θB ρ t (Fin.last (min i j)) ≠ 0 :=
    adj_last_col_ne_zero i j θA θB ρ hρ hE hcop t
  have key : U K i j θA θB ρ 0 (Fin.last (min i j)) * (∑ s, U K i j θA θB ρ t s * Rv s)
      = U K i j θA θB ρ t (Fin.last (min i j)) * (∑ s, U K i j θA θB ρ 0 s * Rv s) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h := minor_two_two hρ hE h00 t s
    calc U K i j θA θB ρ 0 (Fin.last (min i j)) * (U K i j θA θB ρ t s * Rv s)
        = (U K i j θA θB ρ t s * U K i j θA θB ρ 0 (Fin.last (min i j))) * Rv s := by ring
      _ = (U K i j θA θB ρ t (Fin.last (min i j)) * U K i j θA θB ρ 0 s) * Rv s := by rw [h]
      _ = U K i j θA θB ρ t (Fin.last (min i j)) * (U K i j θA θB ρ 0 s * Rv s) := by ring
  constructor
  · intro hz
    rw [hz, mul_zero] at key
    exact (mul_eq_zero.mp key.symm).resolve_left htm
  · intro hz
    rw [hz, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left h0m

theorem residual_criterion_at_root (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (Rv : Fin (min i j + 1) → K) (t : Fin (min i j + 1)) :
    (∑ s : Fin (min i j + 1), ell K i j θA θB ρ (s : ℕ) * Rv s) ≠ 0
      ↔ (∑ s, U K i j θA θB ρ t s * Rv s) ≠ 0 := by
  have hell : (∑ s : Fin (min i j + 1), ell K i j θA θB ρ (s : ℕ) * Rv s)
      = ∑ s, U K i j θA θB ρ 0 s * Rv s :=
    Finset.sum_congr rfl fun s _ => by rw [U_zero_apply]
  rw [hell, not_iff_not]
  exact (level_free_at_root i j θA θB ρ hρ hE hcop Rv t).symm

end AtRoot

end Rhone.Analysis.DenominatorEquation
