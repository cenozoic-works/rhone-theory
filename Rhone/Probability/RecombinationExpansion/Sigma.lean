/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Kernel

/-! # Well-posedness and uniqueness of the `σ` recursion -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

variable {KA KB : ℕ} {F : Type*} [Field F] [CharZero F]

structure IsSigma (S σ : Config KA KB → F) : Prop where
  bdry : ∀ ξ : Config KA KB, ξ.t = 0 → σ ξ = 0
  step : ∀ ξ : Config KA KB, ξ.t ≠ 0 →
    ((ξ.t : ℕ) : F) * σ ξ
      = (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * σ (ξ.split i j)) + S ξ

theorem IsSigma.unique {S σ₁ σ₂ : Config KA KB → F} (h₁ : IsSigma S σ₁) (h₂ : IsSigma S σ₂) :
    σ₁ = σ₂ := by
  have key : ∀ n : ℕ, ∀ ξ : Config KA KB, ξ.t = n → σ₁ ξ = σ₂ ξ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ξ hn
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · rw [h₁.bdry ξ (by omega), h₂.bdry ξ (by omega)]
      · have hne : ξ.t ≠ 0 := by omega
        have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
            ((ξ.c i j : ℕ) : F) * σ₁ (ξ.split i j)
              = ((ξ.c i j : ℕ) : F) * σ₂ (ξ.split i j) := by
          intro i j
          by_cases hc : ξ.c i j = 0
          · rw [hc]; simp
          · have hlt : (ξ.split i j).t < n := by have := ξ.t_split i j hc; omega
            rw [ih _ hlt (ξ.split i j) rfl]
        have e₁ := h₁.step ξ hne
        have e₂ := h₂.step ξ hne
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j] at e₁
        have hcast : ((ξ.t : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hne
        have : ((ξ.t : ℕ) : F) * (σ₁ ξ - σ₂ ξ) = 0 := by
          rw [mul_sub, e₁, e₂, sub_self]
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hcast)
  funext ξ
  exact key ξ.t ξ rfl

noncomputable def sigmaAux (S : Config KA KB → F) : ℕ → Config KA KB → F
  | 0, _ => 0
  | (k + 1), ξ =>
      if ξ.t = 0 then 0
      else ((ξ.t : ℕ) : F)⁻¹
        * ((∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * sigmaAux S k (ξ.split i j)) + S ξ)

omit [CharZero F] in
theorem sigmaAux_zero (S : Config KA KB → F) (ξ : Config KA KB) : sigmaAux S 0 ξ = 0 := rfl

omit [CharZero F] in
theorem sigmaAux_succ (S : Config KA KB → F) (k : ℕ) (ξ : Config KA KB) :
    sigmaAux S (k + 1) ξ
      = if ξ.t = 0 then 0
        else ((ξ.t : ℕ) : F)⁻¹
          * ((∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * sigmaAux S k (ξ.split i j)) + S ξ) := rfl

theorem sigmaAux_congr (S : Config KA KB → F) :
    ∀ k l : ℕ, ∀ ξ : Config KA KB, ξ.t ≤ k → ξ.t ≤ l → sigmaAux S k ξ = sigmaAux S l ξ := by
  intro k
  induction k with
  | zero =>
    intro l ξ hk _
    have ht : ξ.t = 0 := by omega
    match l with
    | 0 => rfl
    | (l' + 1) => rw [sigmaAux_zero, sigmaAux_succ, ite_eq_left ht]
  | succ k ih =>
    intro l ξ hk hl
    by_cases ht : ξ.t = 0
    · match l with
      | 0 => rw [sigmaAux_zero, sigmaAux_succ, ite_eq_left ht]
      | (l' + 1) => rw [sigmaAux_succ, sigmaAux_succ, ite_eq_left ht, ite_eq_left ht]
    · match l with
      | 0 => omega
      | (l' + 1) =>
        rw [sigmaAux_succ, sigmaAux_succ, ite_eq_right ht, ite_eq_right ht]
        congr 2
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases hc : ξ.c i j = 0
        · rw [hc]; simp
        · have hstep := ξ.t_split i j hc
          rw [ih l' (ξ.split i j) (by omega) (by omega)]

noncomputable def sigmaSol (S : Config KA KB → F) (ξ : Config KA KB) : F :=
  sigmaAux S ξ.t ξ

omit [CharZero F] in
theorem sigmaSol_of_t_eq_zero {S : Config KA KB → F} {ξ : Config KA KB} (ht : ξ.t = 0) :
    sigmaSol S ξ = 0 := by
  rw [sigmaSol, ht, sigmaAux_zero]

theorem sigmaSol_eq_aux (S : Config KA KB → F) {k : ℕ} {ξ : Config KA KB} (hk : ξ.t ≤ k) :
    sigmaSol S ξ = sigmaAux S k ξ :=
  sigmaAux_congr S ξ.t k ξ (le_refl _) hk

theorem sigmaSol_isSigma (S : Config KA KB → F) : IsSigma S (sigmaSol S) := by
  refine ⟨fun ξ ht => sigmaSol_of_t_eq_zero ht, fun ξ hne => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, ξ.t = r + 1 := ⟨ξ.t - 1, by omega⟩
  have hval : sigmaSol S ξ
      = ((ξ.t : ℕ) : F)⁻¹
        * ((∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * sigmaAux S r (ξ.split i j)) + S ξ) := by
    rw [sigmaSol_eq_aux S (le_of_eq hr), sigmaAux_succ, ite_eq_right hne]
  have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
      ((ξ.c i j : ℕ) : F) * sigmaAux S r (ξ.split i j)
        = ((ξ.c i j : ℕ) : F) * sigmaSol S (ξ.split i j) := by
    intro i j
    by_cases hc : ξ.c i j = 0
    · rw [hc]; simp
    · have hstep := ξ.t_split i j hc
      rw [sigmaSol_eq_aux S (k := r) (by omega)]
  rw [hval, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j,
    ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hne), one_mul]

theorem existsUnique_isSigma (S : Config KA KB → F) : ∃! σ : Config KA KB → F, IsSigma S σ :=
  ⟨sigmaSol S, sigmaSol_isSigma S, fun _ h => h.unique (sigmaSol_isSigma S)⟩

omit [CharZero F] in
theorem IsSigma.L1_eq {S σ : Config KA KB → F} (h : IsSigma S σ)
    (hS : ∀ ξ : Config KA KB, ξ.t = 0 → S ξ = 0) (ξ : Config KA KB) : L1 σ ξ = S ξ := by
  by_cases ht : ξ.t = 0
  · rw [L1_of_t_eq_zero σ ht, hS ξ ht]
  · have := h.step ξ ht
    rw [L1]
    linear_combination this

omit [CharZero F] in
theorem isSigma_of_L1_eq {S σ : Config KA KB → F} (hb : ∀ ξ : Config KA KB, ξ.t = 0 → σ ξ = 0)
    (h : ∀ ξ : Config KA KB, L1 σ ξ = S ξ) : IsSigma S σ := by
  refine ⟨hb, fun ξ _ => ?_⟩
  have := h ξ
  rw [L1] at this
  linear_combination this

theorem sigmaOf_eq_sigmaSol {S q2 : Config KA KB → F}
    (h : ∀ ξ : Config KA KB, L1 q2 ξ = S ξ) : sigmaOf q2 = sigmaSol S :=
  (isSigma_of_L1_eq (fun ξ ht => sigma_t_zero q2 ht)
    (fun ξ => by rw [sigma_L1 q2 ξ, h ξ])).unique (sigmaSol_isSigma S)

end Rhone.Probability.RecombinationExpansion
