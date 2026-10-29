/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Vertex

/-! # The one-locus rare-allele coefficients `α^i`, `β^j` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial

section Seq

variable {K : Type*} [Field K]

noncomputable def alphaSeq (θ : K) (i : ℕ) : K :=
  (Nat.factorial (i - 1) : K) / ∏ k ∈ Finset.Ico 1 i, (θ + (k : K))

@[simp] theorem alphaSeq_one (θ : K) : alphaSeq θ 1 = 1 := by
  simp [alphaSeq]

theorem alphaSeq_two (θ : K) : alphaSeq θ 2 = 1 / (θ + 1) := by
  rw [alphaSeq]
  norm_num

end Seq

section OneLocus

variable {K : Type*} [Field K] [CharZero K] {θA θB ρ : K}
variable {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem recursionSource_one_locus (Ψ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) (i : ℕ) :
    recursionSource kapX gamX kapY gamY Ψ i 0 0
      = kapX * (((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K) * Ψ (i - 2) 0 0)
        + gamX * (((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K)) * Ψ (i - 1) 0 0 := by
  simp only [recursionSource]
  norm_num

theorem dcoef_one_locus (i : ℕ) :
    LinearAlgebra.Tridiag.dcoef K i 0 θA θB ρ 0 = ((i * (i - 1) : ℕ) : K) + θA * (i : K) := by
  simp [LinearAlgebra.Tridiag.dcoef]

theorem one_locus_row (hD : IsRecursionSolution θA θB ρ Φ) (i : ℕ) :
    (((i * (i - 1) : ℕ) : K) + θA * (i : K)) * cf 1 0 (Φ i 0 0)
      = ((i * (i - 1) : ℕ) : K) * (cf 0 0 (Φ (i - 2) 0 0)
          + (cf 1 0 (Φ (i - 1) 0 0) - 2 * cf 0 0 (Φ (i - 1) 0 0))) := by
  have hrow := hD i 0 0 (by simp)
  rw [recursionSource_one_locus] at hrow
  have hrow2 : C (LinearAlgebra.Tridiag.dcoef K i 0 θA θB ρ 0) * Φ i 0 0
      = kapX * (((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K) * Φ (i - 2) 0 0)
        + gamX * (((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K)) * Φ (i - 1) 0 0 := by
    rw [← hrow]
    norm_num
  have hcf := congrArg (cf 1 0) hrow2
  rw [cf_C_mul, cf_add, cf10_kapX_mul, cf_natCast_mul, mul_assoc, cf10_gamX_mul,
    cf_natCast_mul, cf_natCast_mul, dcoef_one_locus] at hcf
  rw [hcf]
  ring

omit [CharZero K] in
theorem cf10_Phi_one (h1A : ∀ b u : ℕ, Φ 1 b u = 0) : cf 1 0 (Φ 1 0 0) = 0 := by
  rw [h1A 0 0, cf_zero]

theorem alpha_cleared (hD : IsRecursionSolution θA θB ρ Φ)
    (hvan : ∀ a b u : ℕ, 1 ≤ a → Van 0 (Φ a b u))
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h00 : cf 0 0 (Φ 0 0 0) = 1) :
    ∀ i : ℕ, 2 ≤ i →
      (∏ k ∈ Finset.Ico 1 i, (θA + (k : K))) * cf 1 0 (Φ i 0 0)
        = (Nat.factorial (i - 1) : K) := by
  have hvan00 : ∀ a : ℕ, 1 ≤ a → cf 0 0 (Φ a 0 0) = 0 := fun a ha =>
    hvan a 0 0 ha (mon 0 0) (by simp)
  intro i
  induction i with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases Nat.eq_or_lt_of_le hn with h2 | h3
    · have hn1 : n = 1 := by omega
      subst hn1
      have hrow := one_locus_row (θB := θB) (ρ := ρ) hD 2
      norm_num [h00, cf10_Phi_one h1A, hvan00 1 (le_refl 1)] at hrow
      have hprod : (∏ k ∈ Finset.Ico (1 : ℕ) 2, (θA + (k : K))) = θA + 1 := by norm_num
      rw [hprod]
      norm_num
      linear_combination hrow / 2
    · have hn3 : 3 ≤ n + 1 := h3
      have hprev := ih (by omega)
      have hrow := one_locus_row (θB := θB) (ρ := ρ) hD (n + 1)
      rw [hvan00 (n + 1 - 2) (by omega), hvan00 (n + 1 - 1) (by omega)] at hrow
      push_cast at hrow
      have hne : ((n : K) + 1) ≠ 0 := by
        have hnz : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at hnz
        exact hnz
      have hstep : (θA + (n : K)) * cf 1 0 (Φ (n + 1) 0 0) = (n : K) * cf 1 0 (Φ n 0 0) := by
        refine mul_left_cancel₀ hne ?_
        linear_combination hrow
      have hsplit : (∏ k ∈ Finset.Ico 1 (n + 1), (θA + (k : K)))
          = (∏ k ∈ Finset.Ico 1 n, (θA + (k : K))) * (θA + (n : K)) :=
        Finset.prod_Ico_succ_top (by omega) _
      have hfact : (Nat.factorial (n + 1 - 1) : K) = (n : K) * (Nat.factorial (n - 1) : K) := by
        have h1 : Nat.factorial (n + 1 - 1) = n * Nat.factorial (n - 1) := by
          rw [show n + 1 - 1 = n from rfl]
          conv_lhs => rw [show n = (n - 1) + 1 from by omega]
          rw [Nat.factorial_succ, show n - 1 + 1 = n from by omega]
        rw [h1]
        push_cast
        ring
      rw [hsplit, hfact]
      calc (∏ k ∈ Finset.Ico 1 n, (θA + (k : K))) * (θA + (n : K)) * cf 1 0 (Φ (n + 1) 0 0)
          = (∏ k ∈ Finset.Ico 1 n, (θA + (k : K)))
              * ((θA + (n : K)) * cf 1 0 (Φ (n + 1) 0 0)) := by ring
        _ = (∏ k ∈ Finset.Ico 1 n, (θA + (k : K))) * ((n : K) * cf 1 0 (Φ n 0 0)) := by
              rw [hstep]
        _ = (n : K) * ((∏ k ∈ Finset.Ico 1 n, (θA + (k : K))) * cf 1 0 (Φ n 0 0)) := by ring
        _ = (n : K) * (Nat.factorial (n - 1) : K) := by rw [hprev]

theorem alpha_eq_alphaSeq (hD : IsRecursionSolution θA θB ρ Φ)
    (hvan : ∀ a b u : ℕ, 1 ≤ a → Van 0 (Φ a b u))
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h00 : cf 0 0 (Φ 0 0 0) = 1)
    {i : ℕ} (hi : 2 ≤ i) (hP : (∏ k ∈ Finset.Ico 1 i, (θA + (k : K))) ≠ 0) :
    cf 1 0 (Φ i 0 0) = alphaSeq θA i := by
  have h := alpha_cleared hD hvan h1A h00 i hi
  rw [alphaSeq, eq_div_iff hP]
  linear_combination h

end OneLocus

section Mirror

variable {K : Type*} [Field K] [CharZero K] {θA θB ρ : K}
variable {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem beta_cleared (hD : IsRecursionSolution θA θB ρ Φ)
    (hvanB : ∀ a b u : ℕ, 1 ≤ b → Van 1 (Φ a b u))
    (h1B : ∀ a u : ℕ, Φ a 1 u = 0) (h00 : cf 0 0 (Φ 0 0 0) = 1) :
    ∀ j : ℕ, 2 ≤ j →
      (∏ k ∈ Finset.Ico 1 j, (θB + (k : K))) * cf 0 1 (Φ 0 j 0)
        = (Nat.factorial (j - 1) : K) := by
  intro j hj
  have hswap := alpha_cleared (θA := θB) (θB := θA) (ρ := ρ)
    (Φ := fun a b u => rename swp (Φ b a u)) (isRecursionSolution_swap hD) ?_ ?_ ?_ j hj
  · rwa [cf_rename_swp] at hswap
  · intro a b u ha
    exact Van_rename_swp (by simpa using hvanB b a u ha)
  · intro b u
    rw [h1B b u, map_zero]
  · rw [cf_rename_swp, h00]

theorem beta_eq_alphaSeq (hD : IsRecursionSolution θA θB ρ Φ)
    (hvanB : ∀ a b u : ℕ, 1 ≤ b → Van 1 (Φ a b u))
    (h1B : ∀ a u : ℕ, Φ a 1 u = 0) (h00 : cf 0 0 (Φ 0 0 0) = 1)
    {j : ℕ} (hj : 2 ≤ j) (hP : (∏ k ∈ Finset.Ico 1 j, (θB + (k : K))) ≠ 0) :
    cf 0 1 (Φ 0 j 0) = alphaSeq θB j := by
  have h := beta_cleared hD hvanB h1B h00 j hj
  rw [alphaSeq, eq_div_iff hP]
  linear_combination h

end Mirror

end Rhone.Probability.RareAlleleHierarchy
