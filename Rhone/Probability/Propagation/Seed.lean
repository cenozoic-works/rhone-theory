/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Kernel
public import Rhone.Probability.SlotDeletion.Matrix

/-! # The seed: the residue at the base block is the kernel column `adj(T)_{·,0}` -/

@[expose] public section

namespace Rhone.Probability.Propagation

open Matrix LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation

variable (K : Type*) [Field K]

def vker (i j : ℕ) (θA θB ρ : K) (t : ℕ) : K :=
  usmaniEntry (dcoef K i j θA θB ρ) (bcoef K i j) (ccoef K ρ) (min i j + 1) t 0

variable {K}

theorem vker_eq_U (i j : ℕ) (θA θB ρ : K) (t : Fin (min i j + 1)) :
    vker K i j θA θB ρ (t : ℕ) = U K i j θA θB ρ t 0 := by
  rw [vker, U_apply]
  rfl

theorem vker_eq (i j : ℕ) (θA θB ρ : K) (t : ℕ) :
    vker K i j θA θB ρ t = ρ ^ t * ((Nat.factorial t : ℕ) : K) * DeltaP K i j θA θB ρ (t + 1) := by
  rw [vker, usmaniEntry_T_of_ge i j θA θB ρ (Nat.zero_le t), DeltaP, Nat.sub_zero]
  have h0 : cont (dcoef K i j θA θB ρ) (bcoef K i j) (ccoef K ρ) 0 = 1 := rfl
  rw [h0, mul_one]
  congr 2
  have hfac : (∏ s ∈ Finset.Ico 0 t, (s + 1)) * Nat.factorial 0 = Nat.factorial t :=
    prod_succ_mul_factorial (Nat.zero_le t)
  rw [Nat.factorial_zero, mul_one] at hfac
  rw [← hfac]
  push_cast
  rfl

@[simp]
theorem vker_zero (i j : ℕ) (θA θB ρ : K) :
    vker K i j θA θB ρ 0 = DeltaP K i j θA θB ρ 1 := by
  rw [vker_eq]
  simp

theorem T_mulVec_vker {i j : ℕ} {θA θB ρ : K} (hE : E K i j θA θB ρ = 0) :
    T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => vker K i j θA θB ρ (s : ℕ)) = 0 := by
  funext s
  have hcol : (T K i j θA θB ρ *ᵥ fun t : Fin (min i j + 1) => vker K i j θA θB ρ (t : ℕ)) s
      = (T K i j θA θB ρ * U K i j θA θB ρ) s 0 := by
    simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    exact Finset.sum_congr rfl fun t _ => by rw [vker_eq_U]
  rw [hcol, T_mul_U, hE]
  simp

theorem vker_ne_zero [CharZero K] {i j : ℕ} {θA θB ρ : K} (hρ : ρ ≠ 0)
    (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 → DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    {t : ℕ} (ht : t ≤ min i j) : vker K i j θA θB ρ t ≠ 0 := by
  rw [vker_eq]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hρ) ?_)
    (DeltaP_ne_zero i j θA θB ρ hρ hE hcop ht)
  exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero t)

theorem right_ker_head_zero [CharZero K] {i j : ℕ} {θA θB ρ : K} {Ψ : ℕ → K}
    (hker : T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => Ψ (s : ℕ)) = 0)
    (h0 : Ψ 0 = 0) : ∀ t, t ≤ min i j → Ψ t = 0 := by
  have key : ∀ n : ℕ, ∀ t, t ≤ n → t ≤ min i j → Ψ t = 0 := by
    intro n
    induction n with
    | zero => intro t ht _; rw [show t = 0 from Nat.le_zero.1 ht]; exact h0
    | succ n ih =>
      intro t ht htm
      rcases Nat.lt_or_ge t (n + 1) with hlt | hge
      · exact ih t (by omega) htm
      have htn : t = n + 1 := by omega
      subst htn
      have hn : n < min i j := by omega
      have hrow := congrFun hker (⟨n, by omega⟩ : Fin (min i j + 1))
      rw [Rhone.Probability.SlotDeletion.T_mulVec_apply i j θA θB ρ Ψ ⟨n, by omega⟩] at hrow
      simp only [Pi.zero_apply] at hrow
      rw [ih n (by omega) (by omega), ih (n - 1) (by omega) (by omega)] at hrow
      have hb : (2 : K) * (((i - n) * (j - n) : ℕ) : K) ≠ 0 := by
        refine mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 (Nat.mul_ne_zero ?_ ?_)) <;> omega
      have hz : (2 : K) * (((i - n) * (j - n) : ℕ) : K) * Ψ (n + 1) = 0 := by
        linear_combination -hrow
      exact (mul_eq_zero.1 hz).resolve_left hb
  intro t ht
  exact key t t le_rfl ht

theorem right_ker_eq_smul_vker [CharZero K] {i j : ℕ} {θA θB ρ : K} {Ψ : ℕ → K} (hρ : ρ ≠ 0)
    (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 → DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (hker : T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => Ψ (s : ℕ)) = 0)
    {t : ℕ} (ht : t ≤ min i j) :
    Ψ t = (Ψ 0 / vker K i j θA θB ρ 0) * vker K i j θA θB ρ t := by
  set c : K := Ψ 0 / vker K i j θA θB ρ 0 with hc
  have hv0 : vker K i j θA θB ρ 0 ≠ 0 := vker_ne_zero hρ hE hcop (Nat.zero_le _)
  have hdiff : T K i j θA θB ρ
      *ᵥ (fun s : Fin (min i j + 1) => Ψ (s : ℕ) - c * vker K i j θA θB ρ (s : ℕ)) = 0 := by
    have hsplit : (fun s : Fin (min i j + 1) => Ψ (s : ℕ) - c * vker K i j θA θB ρ (s : ℕ))
        = (fun s : Fin (min i j + 1) => Ψ (s : ℕ))
          - c • (fun s : Fin (min i j + 1) => vker K i j θA θB ρ (s : ℕ)) := by
      funext s; simp
    rw [hsplit, Matrix.mulVec_sub, Matrix.mulVec_smul, hker, T_mulVec_vker hE]
    simp
  have h0 : Ψ 0 - c * vker K i j θA θB ρ 0 = 0 := by
    rw [hc, div_mul_cancel₀ _ hv0, sub_self]
  have hfin := right_ker_head_zero (Ψ := fun s => Ψ s - c * vker K i j θA θB ρ s) hdiff h0 t ht
  linear_combination hfin

variable {i j : ℕ} {θA θB ρ : K} {Ψ : ℕ → K}

theorem res_base_eq_smul_vker [CharZero K] (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 → DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (hker : T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => Ψ (s : ℕ)) = 0) :
    ∃ c : K, ∀ t, t ≤ min i j → Ψ t = c * vker K i j θA θB ρ t :=
  ⟨Ψ 0 / vker K i j θA θB ρ 0, fun _ ht => right_ker_eq_smul_vker hρ hE hcop hker ht⟩

theorem res_base_smul_unique [CharZero K] (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 → DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    {c c' : K} (h : ∀ t, t ≤ min i j → c * vker K i j θA θB ρ t = c' * vker K i j θA θB ρ t) :
    c = c' :=
  mul_right_cancel₀ (vker_ne_zero hρ hE hcop (Nat.zero_le _)) (h 0 (Nat.zero_le _))

theorem res_base_ne_zero_iff [CharZero K] (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 → DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    (hker : T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => Ψ (s : ℕ)) = 0) :
    (∃ t, t ≤ min i j ∧ Ψ t ≠ 0) ↔ ∀ t, t ≤ min i j → Ψ t ≠ 0 := by
  obtain ⟨c, hcv⟩ := res_base_eq_smul_vker hρ hE hcop hker
  constructor
  · rintro ⟨t, ht, hne⟩ s hs
    have hc : c ≠ 0 := by
      intro hc0
      exact hne (by rw [hcv t ht, hc0, zero_mul])
    rw [hcv s hs]
    exact mul_ne_zero hc (vker_ne_zero hρ hE hcop hs)
  · intro h
    exact ⟨0, Nat.zero_le _, h 0 (Nat.zero_le _)⟩

end Rhone.Probability.Propagation
