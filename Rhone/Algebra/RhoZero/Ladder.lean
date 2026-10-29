/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # The local leading coefficient is the top rung of the renewal ladder -/

@[expose] public section

namespace Rhone.Algebra.RhoZero

open Finset

structure System (V : Type*) [Fintype V] [DecidableEq V] (O : Type*) [CommRing O] where
  rk : V → ℕ
  fuel : ℕ
  hfuel : ∀ ξ, rk ξ < fuel
  T : Finset V
  A : Finset V
  hTA : ∀ ξ, ξ ∈ A → ξ ∉ T
  cf : V → V → O
  hcf : ∀ ξ v, cf ξ v ≠ 0 → rk v < rk ξ
  d : V → O
  dinv : V → O
  hdinv : ∀ ξ, ξ ∉ T → ξ ∉ A → d ξ * dinv ξ = 1
  cA : V → O
  cAinv : V → O
  hcA : ∀ ξ, ξ ∈ A → cA ξ * cAinv ξ = 1
  ell : O
  hdA : ∀ ξ, ξ ∈ A → d ξ = cA ξ * ell
  qhat : V → O

variable {V : Type*} [Fintype V] [DecidableEq V] {O : Type*} [CommRing O]

namespace System

def avoidAux (S : System V O) (g h : V → O) : ℕ → V → O
  | 0, _ => 0
  | m + 1, ξ =>
      if ξ ∈ S.T then g ξ
      else if ξ ∈ S.A then h ξ
      else S.dinv ξ * ∑ v, S.cf ξ v * S.avoidAux g h m v

theorem avoidAux_stab (S : System V O) (g h : V → O) :
    ∀ (m m' : ℕ) (ξ : V), S.rk ξ < m → m ≤ m' → S.avoidAux g h m ξ = S.avoidAux g h m' ξ := by
  intro m
  induction m with
  | zero => intro _ ξ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ m₀ IH =>
    intro m' ξ hlt hle
    obtain ⟨m₀', rfl⟩ : ∃ m₀', m' = m₀' + 1 := ⟨m' - 1, by omega⟩
    have hle' : m₀ ≤ m₀' := by omega
    simp only [avoidAux]
    by_cases hT : ξ ∈ S.T
    · rw [ite_eq_left hT, ite_eq_left hT]
    by_cases hA : ξ ∈ S.A
    · rw [ite_eq_right hT, ite_eq_right hT, ite_eq_left hA, ite_eq_left hA]
    rw [ite_eq_right hT, ite_eq_right hT, ite_eq_right hA, ite_eq_right hA]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hcf : S.cf ξ v = 0
    · rw [hcf, zero_mul, zero_mul]
    · have := S.hcf ξ v hcf
      rw [IH m₀' v (by omega) hle']

theorem avoidAux_succ (S : System V O) (g h : V → O) (m : ℕ) (ξ : V) :
    S.avoidAux g h (m + 1) ξ =
      if ξ ∈ S.T then g ξ
      else if ξ ∈ S.A then h ξ
      else S.dinv ξ * ∑ v, S.cf ξ v * S.avoidAux g h m v := rfl

def avoid (S : System V O) (g h : V → O) (ξ : V) : O := S.avoidAux g h S.fuel ξ

theorem avoid_eq (S : System V O) (g h : V → O) (ξ : V) :
    S.avoid g h ξ =
      if ξ ∈ S.T then g ξ
      else if ξ ∈ S.A then h ξ
      else S.dinv ξ * ∑ v, S.cf ξ v * S.avoid g h v := by
  have hf : S.rk ξ < S.fuel := S.hfuel ξ
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, S.fuel = f₀ + 1 := ⟨S.fuel - 1, by omega⟩
  have hhead : S.avoid g h ξ = S.avoidAux g h (f₀ + 1) ξ := by simp only [avoid, hf₀]
  rw [hhead, avoidAux_succ]
  by_cases hT : ξ ∈ S.T
  · rw [ite_eq_left hT, ite_eq_left hT]
  by_cases hA : ξ ∈ S.A
  · rw [ite_eq_right hT, ite_eq_right hT, ite_eq_left hA, ite_eq_left hA]
  rw [ite_eq_right hT, ite_eq_right hT, ite_eq_right hA, ite_eq_right hA]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hcf : S.cf ξ v = 0
  · rw [hcf, zero_mul, zero_mul]
  · have hrk := S.hcf ξ v hcf
    have hv : S.avoid g h v = S.avoidAux g h (f₀ + 1) v := by simp only [avoid, hf₀]
    rw [hv, S.avoidAux_stab g h f₀ (f₀ + 1) v (by omega) (by omega)]

theorem avoid_of_mem_T (S : System V O) (g h : V → O) {ξ : V} (hT : ξ ∈ S.T) :
    S.avoid g h ξ = g ξ := by rw [S.avoid_eq g h ξ, ite_eq_left hT]

theorem avoid_of_mem_A (S : System V O) (g h : V → O) {ξ : V} (hA : ξ ∈ S.A) :
    S.avoid g h ξ = h ξ := by
  rw [S.avoid_eq g h ξ, ite_eq_right (S.hTA ξ hA), ite_eq_left hA]

theorem avoid_of_interior (S : System V O) (g h : V → O) {ξ : V} (hT : ξ ∉ S.T) (hA : ξ ∉ S.A) :
    S.avoid g h ξ = S.dinv ξ * ∑ v, S.cf ξ v * S.avoid g h v := by
  rw [S.avoid_eq g h ξ, ite_eq_right hT, ite_eq_right hA]

def W (S : System V O) : ℕ → V → O
  | 0 => S.avoid S.qhat (fun _ => 0)
  | m + 1 => S.avoid (fun _ => 0) (fun ξ => S.cAinv ξ * ∑ v, S.cf ξ v * S.W m v)

def rung (S : System V O) (m : ℕ) (ξ : V) : O := S.cAinv ξ * ∑ v, S.cf ξ v * S.W m v

theorem W_succ (S : System V O) (m : ℕ) : S.W (m + 1) = S.avoid (fun _ => 0) (S.rung m) := rfl

def Q (S : System V O) (M : ℕ) (ξ : V) : O :=
  ∑ m ∈ Finset.range (M + 1), S.ell ^ (M - m) * S.W m ξ

theorem W_of_mem_T (S : System V O) {ξ : V} (hT : ξ ∈ S.T) :
    ∀ m : ℕ, S.W m ξ = if m = 0 then S.qhat ξ else 0 := by
  intro m
  cases m with
  | zero => simpa [W] using S.avoid_of_mem_T S.qhat (fun _ => 0) hT
  | succ m =>
    rw [S.W_succ m, S.avoid_of_mem_T (fun _ => (0 : O)) (S.rung m) hT,
      ite_eq_right (Nat.succ_ne_zero m)]

theorem W_of_mem_A (S : System V O) {ξ : V} (hA : ξ ∈ S.A) :
    ∀ m : ℕ, S.W m ξ = if m = 0 then 0 else S.rung (m - 1) ξ := by
  intro m
  cases m with
  | zero => simpa [W] using S.avoid_of_mem_A S.qhat (fun _ => (0 : O)) hA
  | succ m =>
    rw [S.W_succ m, S.avoid_of_mem_A (fun _ => (0 : O)) (S.rung m) hA,
      ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]

theorem W_of_interior (S : System V O) {ξ : V} (hT : ξ ∉ S.T) (hA : ξ ∉ S.A) (m : ℕ) :
    S.W m ξ = S.dinv ξ * ∑ v, S.cf ξ v * S.W m v := by
  cases m with
  | zero => exact S.avoid_of_interior S.qhat (fun _ => 0) hT hA
  | succ m => exact S.avoid_of_interior (fun _ => 0) (S.rung m) hT hA

theorem Q_of_mem_T (S : System V O) {ξ : V} (hT : ξ ∈ S.T) (M : ℕ) :
    S.Q M ξ = S.ell ^ M * S.qhat ξ := by
  simp only [Q]
  rw [Finset.sum_eq_single 0]
  · simp [S.W_of_mem_T hT 0]
  · intro m _ hm
    rw [S.W_of_mem_T hT m, ite_eq_right hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos M)) h

theorem cA_mul_rung (S : System V O) {ξ : V} (hA : ξ ∈ S.A) (m : ℕ) :
    S.cA ξ * S.rung m ξ = ∑ v, S.cf ξ v * S.W m v := by
  simp only [rung]
  rw [← mul_assoc, S.hcA ξ hA, one_mul]

theorem Q_rec (S : System V O) (M : ℕ) (hvan : ∀ ξ ∈ S.A, S.rung M ξ = 0) (ξ : V)
    (hT : ξ ∉ S.T) : S.d ξ * S.Q M ξ = ∑ v, S.cf ξ v * S.Q M v := by
  have hswap : ∑ v, S.cf ξ v * S.Q M v
      = ∑ m ∈ Finset.range (M + 1), S.ell ^ (M - m) * ∑ v, S.cf ξ v * S.W m v := by
    simp only [Q, Finset.mul_sum, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Finset.sum_congr rfl fun v _ => by ring
  by_cases hA : ξ ∈ S.A
  · have hW0 : S.W 0 ξ = 0 := by rw [S.W_of_mem_A hA 0, ite_eq_left rfl]
    have hWs : ∀ m : ℕ, S.W (m + 1) ξ = S.rung m ξ := by
      intro m
      rw [S.W_of_mem_A hA (m + 1), ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]
    have hleft : S.Q M ξ = ∑ m ∈ Finset.range M, S.ell ^ (M - (m + 1)) * S.rung m ξ := by
      simp only [Q]
      rw [Finset.sum_range_succ']
      simp only [hWs, hW0, mul_zero, add_zero]
    rw [hleft, S.hdA ξ hA, hswap]
    have hright : ∑ m ∈ Finset.range (M + 1), S.ell ^ (M - m) * ∑ v, S.cf ξ v * S.W m v
        = S.cA ξ * ∑ m ∈ Finset.range M, S.ell ^ (M - m) * S.rung m ξ := by
      rw [Finset.sum_range_succ]
      rw [← S.cA_mul_rung hA M, hvan ξ hA, mul_zero, mul_zero, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← S.cA_mul_rung hA m]
      ring
    rw [hright, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    have hpow : S.ell * S.ell ^ (M - (m + 1)) = S.ell ^ (M - m) := by
      rw [← pow_succ']
      congr 1
      omega
    calc S.cA ξ * S.ell * (S.ell ^ (M - (m + 1)) * S.rung m ξ)
        = S.cA ξ * (S.ell * S.ell ^ (M - (m + 1))) * S.rung m ξ := by ring
      _ = S.cA ξ * (S.ell ^ (M - m) * S.rung m ξ) := by rw [hpow]; ring
  · rw [hswap]
    simp only [Q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [S.W_of_interior hT hA m]
    calc S.d ξ * (S.ell ^ (M - m) * (S.dinv ξ * ∑ v, S.cf ξ v * S.W m v))
        = S.d ξ * S.dinv ξ * (S.ell ^ (M - m) * ∑ v, S.cf ξ v * S.W m v) := by ring
      _ = S.ell ^ (M - m) * ∑ v, S.cf ξ v * S.W m v := by
          rw [S.hdinv ξ hT hA, one_mul]
      _ = ∑ v, S.ell ^ (M - m) * (S.cf ξ v * S.W m v) := by rw [Finset.mul_sum]

variable [IsDomain O]

theorem eq_of_rec (S : System V O) (hd : ∀ ξ, ξ ∉ S.T → S.d ξ ≠ 0) (f g : V → O)
    (hfT : ∀ ξ ∈ S.T, f ξ = g ξ)
    (hf : ∀ ξ, ξ ∉ S.T → S.d ξ * f ξ = ∑ v, S.cf ξ v * f v)
    (hg : ∀ ξ, ξ ∉ S.T → S.d ξ * g ξ = ∑ v, S.cf ξ v * g v) : ∀ ξ, f ξ = g ξ := by
  have main : ∀ N : ℕ, ∀ ξ : V, S.rk ξ = N → f ξ = g ξ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro ξ hrk
      by_cases hT : ξ ∈ S.T
      · exact hfT ξ hT
      have hsub : ∀ v : V, S.cf ξ v * f v = S.cf ξ v * g v := by
        intro v
        by_cases hcf : S.cf ξ v = 0
        · rw [hcf, zero_mul, zero_mul]
        · rw [IH (S.rk v) (by rw [← hrk]; exact S.hcf ξ v hcf) v rfl]
      have heq : S.d ξ * f ξ = S.d ξ * g ξ := by
        rw [hf ξ hT, hg ξ hT]
        exact Finset.sum_congr rfl fun v _ => hsub v
      exact mul_left_cancel₀ (hd ξ hT) heq
  exact fun ξ => main (S.rk ξ) ξ rfl

theorem ell_pow_mul_q_eq (S : System V O) (hd : ∀ ξ, ξ ∉ S.T → S.d ξ ≠ 0) (q : V → O)
    (hqT : ∀ ξ ∈ S.T, q ξ = S.qhat ξ)
    (hqrec : ∀ ξ, ξ ∉ S.T → S.d ξ * q ξ = ∑ v, S.cf ξ v * q v)
    (M : ℕ) (hvan : ∀ ξ ∈ S.A, S.rung M ξ = 0) (ξ : V) :
    S.ell ^ M * q ξ = S.Q M ξ := by
  refine eq_of_rec S hd (fun v => S.ell ^ M * q v) (S.Q M) ?_ ?_ (S.Q_rec M hvan) ξ
  · intro v hv
    rw [hqT v hv, S.Q_of_mem_T hv]
  · intro v hv
    calc S.d v * (S.ell ^ M * q v) = S.ell ^ M * (S.d v * q v) := by ring
      _ = S.ell ^ M * ∑ w, S.cf v w * q w := by rw [hqrec v hv]
      _ = ∑ w, S.cf v w * (S.ell ^ M * q w) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring

theorem lead_eq_ladder (S : System V O) (hd : ∀ ξ, ξ ∉ S.T → S.d ξ ≠ 0) (q : V → O)
    (hqT : ∀ ξ ∈ S.T, q ξ = S.qhat ξ)
    (hqrec : ∀ ξ, ξ ∉ S.T → S.d ξ * q ξ = ∑ v, S.cf ξ v * q v)
    (M : ℕ) (hvan : ∀ ξ ∈ S.A, S.rung M ξ = 0) (ξ : V) :
    S.ell ∣ (S.ell ^ M * q ξ - S.W M ξ) := by
  rw [ell_pow_mul_q_eq S hd q hqT hqrec M hvan ξ]
  have hsplit : S.Q M ξ - S.W M ξ
      = ∑ m ∈ Finset.range M, S.ell ^ (M - m) * S.W m ξ := by
    simp only [Q]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    ring
  rw [hsplit]
  refine Finset.dvd_sum fun m hm => ?_
  rw [Finset.mem_range] at hm
  refine Dvd.dvd.mul_right ?_ _
  exact dvd_pow_self S.ell (by omega)

theorem ord_ge_of_ladder_zero (S : System V O) (hd : ∀ ξ, ξ ∉ S.T → S.d ξ ≠ 0)
    (hell : S.ell ≠ 0) (q : V → O)
    (hqT : ∀ ξ ∈ S.T, q ξ = S.qhat ξ)
    (hqrec : ∀ ξ, ξ ∉ S.T → S.d ξ * q ξ = ∑ v, S.cf ξ v * q v)
    (M : ℕ) (hM : 1 ≤ M) (hvan : ∀ ξ ∈ S.A, S.rung M ξ = 0)
    (hzero : ∀ ξ, S.W M ξ = 0) (ξ : V) :
    S.ell ^ (M - 1) * q ξ = S.Q (M - 1) ξ := by
  have hkey : S.ell * (S.ell ^ (M - 1) * q ξ) = S.ell * S.Q (M - 1) ξ := by
    have hpow : S.ell * S.ell ^ (M - 1) = S.ell ^ M := by
      rw [← pow_succ']
      congr 1
      omega
    calc S.ell * (S.ell ^ (M - 1) * q ξ) = S.ell ^ M * q ξ := by rw [← mul_assoc, hpow]
      _ = S.Q M ξ := ell_pow_mul_q_eq S hd q hqT hqrec M hvan ξ
      _ = ∑ m ∈ Finset.range M, S.ell ^ (M - m) * S.W m ξ := by
          simp only [Q]
          rw [Finset.sum_range_succ, hzero ξ, mul_zero, add_zero]
      _ = S.ell * S.Q (M - 1) ξ := by
          simp only [Q]
          rw [Finset.mul_sum]
          have hM' : M - 1 + 1 = M := by omega
          rw [hM']
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mem_range] at hm
          have hpow' : S.ell * S.ell ^ (M - 1 - m) = S.ell ^ (M - m) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [← mul_assoc, hpow']
  exact mul_left_cancel₀ hell hkey

end System

end Rhone.Algebra.RhoZero
