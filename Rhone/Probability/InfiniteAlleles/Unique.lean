/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Defs
public import Rhone.LinearAlgebra.Recursion.Unique

/-! # Uniqueness of solutions of the infinite-alleles recursion -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F}

theorem one_le_n_of_level {ξ : Config KA KB} (h : 1 ≤ ξ.nA + ξ.nB) : 1 ≤ ξ.n := by
  rcases Nat.eq_zero_or_pos ξ.n with h0 | h0
  · exact absurd ((ξ.n_eq_zero_iff).mp h0) (by omega)
  · exact h0

theorem within_level_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {N : ℕ}
    (hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB → ξ.nA + ξ.nB ≤ N →
      (∀ η : Config KA KB, η.nA + η.nB < ξ.nA + ξ.nB → h η = 0) →
      diag θA θB ρ ξ * h ξ = (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (ξ.mergeAB i j))
        + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.split i j)) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → h ξ = 0 := by
  suffices H : ∀ L : ℕ, L ≤ N → ∀ ξ : Config KA KB, ξ.nA + ξ.nB = L → h ξ = 0 from
    fun ξ hξ => H _ hξ ξ rfl
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro hLN ξ hξ
    have hbelow : ∀ η : Config KA KB, η.nA + η.nB < L → h η = 0 :=
      fun η hη => IH _ hη (by omega) η rfl
    obtain ⟨ζ, hζS, hζmax⟩ :=
      Set.exists_max_image {ζ : Config KA KB | ζ.nA + ζ.nB = L} (fun ζ => |h ζ|)
        (Config.finite_level L) ⟨ξ, hξ⟩
    have hζlev : ζ.nA + ζ.nB = L := hζS
    have hzero : |h ζ| = 0 := by
      by_cases hn : ζ.nA + ζ.nB ≤ 1
      · rw [hbd ζ hn, abs_zero]
      have hlev2 : 2 ≤ ζ.nA + ζ.nB := by omega
      have heq := hrec ζ hlev2 (by omega) (fun η hη => hbelow η (by omega))
      set M : F := |h ζ| with hMdef
      have hMnn : (0 : F) ≤ M := abs_nonneg _
      have hDpos : 0 < diag θA θB ρ ζ :=
        diag_pos hθA hθB hρ (one_le_n_of_level (by omega))
      have hA : |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
        calc |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
            ≤ ∑ i, |∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * M := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              by_cases ha : ζ.a i = 0
              · rw [ζ.coalAB_eq_zero_left j ha]; simp
              by_cases hb : ζ.b j = 0
              · rw [ζ.coalAB_eq_zero_right i hb]; simp
              obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hb
              refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
              change (ζ.mergeAB i j).nA + (ζ.mergeAB i j).nB = L
              omega
          _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
              rw [← ζ.sum_coalAB]
              push_cast
              simp [Finset.sum_mul]
      have hB : |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| ≤ ((ζ.t : ℕ) : F) * M := by
        calc |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
            ≤ ∑ i, |∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * M := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              by_cases hc : ζ.c i j = 0
              · rw [hc]; simp
              obtain ⟨e1, e2⟩ := ζ.split_same hc
              refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
              change (ζ.split i j).nA + (ζ.split i j).nB = L
              omega
          _ = ((ζ.t : ℕ) : F) * M := by
              rw [← ζ.sum_c]
              push_cast
              simp [Finset.sum_mul]
      have habs : diag θA θB ρ ζ * M
          = |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| := by
        rw [← heq, abs_mul, abs_of_pos hDpos]
      have hchain : diag θA θB ρ ζ * M
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) := by
        rw [habs]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_nonneg hρ]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB hρ)
      have hc1 : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) := by
        exact_mod_cast ζ.two_mul_sumA_mul_sumB_le
      have hP : 0 < θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F) := by
        rcases Nat.eq_zero_or_pos ζ.nA with h0 | h0
        · have hb : 0 < ζ.nB := by omega
          have h1 : (0 : F) < θB * ((ζ.nB : ℕ) : F) := mul_pos hθB (by exact_mod_cast hb)
          have h2 : (0 : F) ≤ θA * ((ζ.nA : ℕ) : F) := mul_nonneg hθA.le (Nat.cast_nonneg _)
          linarith
        · have h1 : (0 : F) < θA * ((ζ.nA : ℕ) : F) := mul_pos hθA (by exact_mod_cast h0)
          have h2 : (0 : F) ≤ θB * ((ζ.nB : ℕ) : F) := mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
      have hDge : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F)
          + (θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F)) + ρ * ((ζ.t : ℕ) : F)
          ≤ diag θA θB ρ ζ := by
        simp only [Rhone.LinearAlgebra.Recursion.diag]
        linarith [hc1]
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hDge, hP, hMpos, mul_pos hP hMpos]
    have := hζmax ξ hξ
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

theorem homogeneousIA_eq_zero_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {N : ℕ}
    (hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * h ξ = rhsIA θA θB ρ h ξ) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → h ξ = 0 :=
  within_level_eq_zero hθA hθB hρ hbd
    fun ξ hn hl hbelow => by
      rw [hrec ξ hn hl]
      exact rhsIA_of_vanishing_below θA θB ρ ξ fun η h1 h2 _ => hbelow η (by omega)

theorem homogeneousIA_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F}
    (hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB →
      diag θA θB ρ ξ * h ξ = rhsIA θA θB ρ h ξ) :
    ∀ ξ : Config KA KB, h ξ = 0 := fun ξ =>
  homogeneousIA_eq_zero_le (N := ξ.nA + ξ.nB) hθA hθB hρ hbd
    (fun η hη _ => hrec η hη) ξ le_rfl

theorem level_le_one_cases (ξ : Config KA KB) (h : ξ.nA + ξ.nB ≤ 1) :
    ξ = 0 ∨ (∃ i, ξ = Config.eA i) ∨ ∃ j, ξ = Config.eB j := by
  have hn : ξ.n ≤ 1 := by have := ξ.n_add_t; omega
  rcases Nat.lt_or_ge ξ.n 1 with h1 | h1
  · exact Or.inl (ξ.eq_zero_of_n_eq_zero (by omega))
  · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨i, j, hij⟩
    · exact Or.inr (Or.inl ⟨i, hi⟩)
    · exact Or.inr (Or.inr ⟨j, hj⟩)
    · exfalso
      subst hij
      have hA : (Config.eC i j : Config KA KB).nA = 1 := by
        simp [Config.nA, Config.sumA, Config.t, Config.eC, sum_incC]
      have hB : (Config.eC i j : Config KA KB).nB = 1 := by
        simp [Config.nB, Config.sumB, Config.t, Config.eC, sum_incC]
      omega

theorem IsSolutionIA.unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolutionIA θA θB ρ q₁)
    (h₂ : IsSolutionIA θA θB ρ q₂) : q₁ = q₂ := by
  have hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hξ
    rcases level_le_one_cases ξ hξ with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [h₁.empty, h₂.empty, sub_self]
    · rw [h₁.bdryA, h₂.bdryA, sub_self]
    · rw [h₁.bdryB, h₂.bdryB, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhsIA θA θB ρ (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hξ
    rw [rhsIA_sub, mul_sub, h₁.recursion ξ hξ, h₂.recursion ξ hξ]
  funext ξ
  have := homogeneousIA_eq_zero hθA hθB hρ hbd hrec ξ
  linarith [this]

end Rhone.Probability.InfiniteAlleles
