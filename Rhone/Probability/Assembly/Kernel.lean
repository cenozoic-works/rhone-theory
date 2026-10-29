/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Rescale.Hensel
public import Rhone.Probability.SlotDeletion.Matrix

/-! # The `σ = 0` right kernel is the binomial vector `C(t, t₀)` -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Matrix LinearAlgebra.Tridiag Analysis.Rescale

section Rows

variable {R : Type*} [CommRing R]

theorem Bmat_mulVec_apply (i j : ℕ) (S z : R) (Ψ : ℕ → R) (t : Fin (min i j + 1)) :
    (Bmat R i j S z *ᵥ fun s => Ψ (s : ℕ)) t
      = (S + z * ((t : ℕ) : R)) * Ψ (t : ℕ) - z * ((t : ℕ) : R) * Ψ ((t : ℕ) - 1) := by
  have hsplit : ∀ s : Fin (min i j + 1),
      Bmat R i j S z t s * Ψ (s : ℕ)
        = (if (s : ℕ) = (t : ℕ) then bdiagE R S z (t : ℕ) * Ψ (s : ℕ) else 0)
          + (if (t : ℕ) = (s : ℕ) + 1 then ccoef R z (s : ℕ) * Ψ (s : ℕ) else 0) := by
    intro s
    simp only [Bmat_apply, tridEntry]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [Matrix.mulVec, dotProduct, hsplit]
  rw [Finset.sum_add_distrib,
    Rhone.Probability.SlotDeletion.sum_ite_val (t : ℕ) (fun s => bdiagE R S z (t : ℕ) * Ψ s),
    ite_eq_left t.isLt]
  rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
  · rw [Finset.sum_eq_zero fun s _ => ite_eq_right (by omega), h0]
    simp [bdiagE]
  · obtain ⟨u, hu⟩ : ∃ u, (t : ℕ) = u + 1 := ⟨(t : ℕ) - 1, by omega⟩
    have hcond : ∀ s : Fin (min i j + 1),
        (if (t : ℕ) = (s : ℕ) + 1 then ccoef R z (s : ℕ) * Ψ (s : ℕ) else 0)
          = (if (s : ℕ) = u then ccoef R z (s : ℕ) * Ψ (s : ℕ) else 0) := by
      intro s
      by_cases h : (s : ℕ) = u
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    rw [Finset.sum_congr rfl fun s _ => hcond s,
      Rhone.Probability.SlotDeletion.sum_ite_val u (fun s => ccoef R z s * Ψ s),
      ite_eq_left (by have := t.isLt; omega), bdiagE, ccoef, hu]
    push_cast
    ring

theorem Bmat_vecMul_apply (i j : ℕ) (S z : R) (Ψ : ℕ → R) (t : Fin (min i j + 1)) :
    ((fun s : Fin (min i j + 1) => Ψ (s : ℕ)) ᵥ* Bmat R i j S z) t
      = (S + z * ((t : ℕ) : R)) * Ψ (t : ℕ)
        + (if (t : ℕ) + 1 < min i j + 1 then ccoef R z (t : ℕ) * Ψ ((t : ℕ) + 1) else 0) := by
  have hsplit : ∀ s : Fin (min i j + 1),
      Ψ (s : ℕ) * Bmat R i j S z s t
        = (if (s : ℕ) = (t : ℕ) then bdiagE R S z (s : ℕ) * Ψ (s : ℕ) else 0)
          + (if (s : ℕ) = (t : ℕ) + 1 then ccoef R z (t : ℕ) * Ψ (s : ℕ) else 0) := by
    intro s
    simp only [Bmat_apply, tridEntry]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [Matrix.vecMul, dotProduct, hsplit]
  rw [Finset.sum_add_distrib,
    Rhone.Probability.SlotDeletion.sum_ite_val (t : ℕ) (fun s => bdiagE R S z s * Ψ s),
    Rhone.Probability.SlotDeletion.sum_ite_val ((t : ℕ) + 1) (fun s => ccoef R z (t : ℕ) * Ψ s),
    ite_eq_left t.isLt, bdiagE]

end Rows

theorem choose_sub_mul (t t₀ : ℕ) : (t - t₀) * t.choose t₀ = t * (t - 1).choose t₀ := by
  cases t with
  | zero => simp
  | succ s =>
    have h := Nat.choose_mul_succ_eq s t₀
    simp only [Nat.succ_sub_one]
    rw [Nat.mul_comm (s + 1 - t₀) ((s + 1).choose t₀), ← h, Nat.mul_comm]

section Kernels

variable {k : Type*} [Field k] [CharZero k]

def binomR (t₀ : ℕ) (k : Type*) [Field k] : ℕ → k := fun t => ((t.choose t₀ : ℕ) : k)

def binomL (t₀ : ℕ) (k : Type*) [Field k] : ℕ → k := fun s => (-1) ^ s * ((t₀.choose s : ℕ) : k)

omit [CharZero k] in
@[simp] theorem binomR_lt {t t₀ : ℕ} (h : t < t₀) : binomR t₀ k t = 0 := by
  simp [binomR, Nat.choose_eq_zero_of_lt h]

omit [CharZero k] in
@[simp] theorem binomR_self (t₀ : ℕ) : binomR t₀ k t₀ = 1 := by simp [binomR]

theorem Bmat_mulVec_binomR (i j : ℕ) (S : k) (r : ℕ) :
    Bmat k i j S (z0 S r) *ᵥ (fun t : Fin (min i j + 1) => binomR (r + 1) k (t : ℕ)) = 0 := by
  funext t
  rw [Bmat_mulVec_apply i j S (z0 S r) (binomR (r + 1) k) t]
  set t₀ := r + 1 with ht₀
  set u : ℕ := (t : ℕ) with hu
  have hroot : S + z0 S r * (t₀ : k) = 0 := by
    have h1 : ((t₀ : ℕ) : k) = ((r : k) + 1) := by rw [ht₀]; push_cast; ring
    rw [h1]
    exact fibre_at_root S r
  by_cases hlt : u < t₀
  · rw [binomR_lt hlt, binomR_lt (show u - 1 < t₀ by omega)]
    simp
  · have hge : t₀ ≤ u := by omega
    have hkey : ((u : k) - (t₀ : k)) * binomR t₀ k u = (u : k) * binomR t₀ k (u - 1) := by
      have h0 : ((u - t₀ : ℕ) : k) * binomR t₀ k u = (u : k) * binomR t₀ k (u - 1) := by
        simp only [binomR]
        exact_mod_cast congrArg (fun n : ℕ => (n : k)) (choose_sub_mul u t₀)
      rwa [Nat.cast_sub hge] at h0
    have hexp : (S + z0 S r * (u : k)) * binomR t₀ k u
        - z0 S r * (u : k) * binomR t₀ k (u - 1)
        = (S + z0 S r * (t₀ : k)) * binomR t₀ k u
          + z0 S r * (((u : k) - (t₀ : k)) * binomR t₀ k u
            - (u : k) * binomR t₀ k (u - 1)) := by ring
    rw [hexp, hkey, sub_self, mul_zero, add_zero, hroot, zero_mul]
    rfl

theorem Bmat_vecMul_binomL (i j : ℕ) (S : k) (r : ℕ) (hr : r + 1 ≤ min i j) :
    (fun s : Fin (min i j + 1) => binomL (r + 1) k (s : ℕ)) ᵥ* Bmat k i j S (z0 S r) = 0 := by
  funext t
  rw [Bmat_vecMul_apply i j S (z0 S r) (binomL (r + 1) k) t]
  set t₀ := r + 1 with ht₀
  set u : ℕ := (t : ℕ) with hu
  have hroot : S + z0 S r * (t₀ : k) = 0 := by
    have h1 : ((t₀ : ℕ) : k) = ((r : k) + 1) := by rw [ht₀]; push_cast; ring
    rw [h1]
    exact fibre_at_root S r
  have hlast : (if u + 1 < min i j + 1 then ccoef k (z0 S r) u * binomL t₀ k (u + 1) else 0)
      = ccoef k (z0 S r) u * binomL t₀ k (u + 1) := by
    by_cases h : u + 1 < min i j + 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      have hz : t₀.choose (u + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [binomL, hz]
  rw [hlast]
  by_cases hu0 : u ≤ t₀
  · have habs : ((t₀.choose (u + 1) : ℕ) : k) * ((u : k) + 1)
        = ((t₀.choose u : ℕ) : k) * ((t₀ : k) - (u : k)) := by
      have hc : ((t₀.choose (u + 1) * (u + 1) : ℕ) : k) = ((t₀.choose u * (t₀ - u) : ℕ) : k) :=
        congrArg (fun n : ℕ => (n : k)) (Nat.choose_succ_right_eq t₀ u)
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hu0] at hc
      push_cast at hc ⊢
      linear_combination hc
    have hexp : (S + z0 S r * (u : k)) * binomL t₀ k u + ccoef k (z0 S r) u * binomL t₀ k (u + 1)
        = (-1) ^ u * ((S + z0 S r * (u : k)) * ((t₀.choose u : ℕ) : k)
            + z0 S r * (((t₀.choose (u + 1) : ℕ) : k) * ((u : k) + 1))) := by
      simp only [binomL, ccoef, pow_succ]
      ring
    rw [hexp, habs]
    have hfin : (S + z0 S r * (u : k)) * ((t₀.choose u : ℕ) : k)
        + z0 S r * (((t₀.choose u : ℕ) : k) * ((t₀ : k) - (u : k)))
        = (S + z0 S r * (t₀ : k)) * ((t₀.choose u : ℕ) : k) := by ring
    rw [hfin, hroot, zero_mul, mul_zero]
    rfl
  · have h1 : t₀.choose u = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : t₀.choose (u + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [binomL, h1, h2, Nat.cast_zero, mul_zero, add_zero]
    rfl

theorem binomR_ne_zero (i j : ℕ) (r : ℕ) (hr : r + 1 ≤ min i j) :
    (fun t : Fin (min i j + 1) => binomR (r + 1) k (t : ℕ)) ≠ 0 := by
  intro h
  have hval := congrFun h (⟨r + 1, by omega⟩ : Fin (min i j + 1))
  rw [show ((⟨r + 1, by omega⟩ : Fin (min i j + 1)) : ℕ) = r + 1 from rfl,
    binomR_self (r + 1)] at hval
  exact one_ne_zero hval

end Kernels

end Rhone.Probability.Assembly
