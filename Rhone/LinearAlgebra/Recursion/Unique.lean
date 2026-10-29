/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Block
public import Rhone.LinearAlgebra.Recursion.Finite

/-! # Well-posedness: uniqueness of the solution of the killed-PIM recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

namespace Config

theorem two_mul_sumA_mul_sumB_le (ξ : Config KA KB) :
    2 * (ξ.sumA * ξ.sumB) ≤ ξ.n * (ξ.n - 1) := by
  have hn : ξ.n = ξ.sumA + ξ.sumB + ξ.t := rfl
  rcases Nat.eq_zero_or_pos ξ.sumA with h | h
  · simp [h]
  rcases Nat.eq_zero_or_pos ξ.sumB with h' | h'
  · simp [h']
  obtain ⟨u, hu⟩ : ∃ u, ξ.sumA = u + 1 := ⟨ξ.sumA - 1, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, ξ.sumB = v + 1 := ⟨ξ.sumB - 1, by omega⟩
  have h1 : ξ.n = u + v + ξ.t + 2 := by omega
  have h2 : ξ.n - 1 = u + v + ξ.t + 1 := by omega
  rw [hu, hv, h2, h1]
  calc 2 * ((u + 1) * (v + 1)) ≤ (u + v + 2) * (u + v + 1) := by nlinarith
    _ ≤ (u + v + ξ.t + 2) * (u + v + ξ.t + 1) := Nat.mul_le_mul (by omega) (by omega)

theorem sum_coalAB (ξ : Config KA KB) : ∑ i, ∑ j, ξ.coalAB i j = 2 * (ξ.sumA * ξ.sumB) := by
  have hrow : ∀ i, (∑ j, ξ.coalAB i j) = 2 * ξ.a i * ξ.sumB := by
    intro i
    simp only [Config.coalAB, Config.sumB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i]
  simp only [Config.sumA, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem sum_c (ξ : Config KA KB) : ∑ i, ∑ j, ξ.c i j = ξ.t := rfl

end Config

theorem diag_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {ξ : Config KA KB} (hn : 1 ≤ ξ.n) :
    0 < diag θA θB ρ ξ := by
  have hlev : 1 ≤ ξ.nA + ξ.nB := by have := ξ.n_add_t; omega
  have h1 : (0 : F) ≤ ((ξ.n * (ξ.n - 1) : ℕ) : F) := Nat.cast_nonneg _
  have h2 : (0 : F) ≤ ρ * ((ξ.t : ℕ) : F) := mul_nonneg hρ (Nat.cast_nonneg _)
  have h3 : (0 : F) ≤ θA * ((ξ.nA : ℕ) : F) := mul_nonneg hθA.le (Nat.cast_nonneg _)
  have h4 : (0 : F) ≤ θB * ((ξ.nB : ℕ) : F) := mul_nonneg hθB.le (Nat.cast_nonneg _)
  have hP : 0 < θA * ((ξ.nA : ℕ) : F) + θB * ((ξ.nB : ℕ) : F) := by
    rcases Nat.eq_zero_or_pos ξ.nA with h0 | h0
    · have hb : 0 < ξ.nB := by omega
      have : (0 : F) < θB * ((ξ.nB : ℕ) : F) := mul_pos hθB (by exact_mod_cast hb)
      linarith
    · have : (0 : F) < θA * ((ξ.nA : ℕ) : F) := mul_pos hθA (by exact_mod_cast h0)
      linarith
  simp only [diag]
  linarith

theorem within_block_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {D : Config KA KB → F} {N : ℕ}
    (hD : ∀ ξ : Config KA KB, diag θA θB ρ ξ ≤ D ξ)
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      (∀ η : Config KA KB, η.nA + η.nB < ξ.nA + ξ.nB → h η = 0) →
      D ξ * h ξ = (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (ξ.mergeAB i j))
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
      by_cases hn : ζ.n ≤ 1
      · rw [hbd ζ hn (by omega), abs_zero]
      have hn2 : 2 ≤ ζ.n := by omega
      have hlev2 : 2 ≤ ζ.nA + ζ.nB := by have := ζ.n_add_t; omega
      have heq := hrec ζ hn2 (by omega) (fun η hη => hbelow η (by omega))
      set M : F := |h ζ| with hMdef
      have hMnn : (0 : F) ≤ M := abs_nonneg _
      have hDpos : 0 < D ζ := lt_of_lt_of_le (diag_pos hθA hθB hρ (by omega)) (hD ζ)
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
      have habs : D ζ * M
          = |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| := by
        rw [← heq, abs_mul, abs_of_pos hDpos]
      have hchain : D ζ * M
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
          + (θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F)) + ρ * ((ζ.t : ℕ) : F) ≤ D ζ := by
        have hd := hD ζ
        simp only [diag] at hd
        linarith [hc1]
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hDge, hP, hMpos, mul_pos hP hMpos]
    have := hζmax ξ hξ
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

theorem homogeneous_eq_zero_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {N : ℕ}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * h ξ = rhs θA θB ρ πA πB h ξ) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → h ξ = 0 :=
  within_block_eq_zero hθA hθB hρ (fun _ => le_rfl) hbd
    fun ξ hn hl hbelow => by
      rw [hrec ξ hn hl]
      exact rhs_of_vanishing_below θA θB ρ πA πB ξ fun η h1 h2 h3 => hbelow η (by omega)

theorem homogeneous_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → diag θA θB ρ ξ * h ξ = rhs θA θB ρ πA πB h ξ) :
    ∀ ξ : Config KA KB, h ξ = 0 := fun ξ =>
  homogeneous_eq_zero_le (πA := πA) (πB := πB) (N := ξ.nA + ξ.nB) hθA hθB hρ
    (fun η hη _ => hbd η hη) (fun η hη _ => hrec η hη) ξ le_rfl

theorem IsSolution.unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolution θA θB ρ πA πB q₁)
    (h₂ : IsSolution θA θB ρ πA πB q₂) : q₁ = q₂ := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hn
    rcases Nat.lt_or_ge ξ.n 1 with h | h
    · have : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
      subst this
      rw [h₁.empty, h₂.empty, sub_self]
    · have h1 : ξ.n = 1 := by omega
      rcases ξ.exists_e_of_n_eq_one h1 with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · rw [h₁.bdryA, h₂.bdryA, sub_self]
      · rw [h₁.bdryB, h₂.bdryB, sub_self]
      · rw [h₁.bdryC, h₂.bdryC, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn
    rw [rhs_sub, mul_sub, h₁.recursion ξ hn, h₂.recursion ξ hn]
  funext ξ
  have := homogeneous_eq_zero (πA := πA) (πB := πB) hθA hθB hρ hbd hrec ξ
  linarith [this]

end Rhone.LinearAlgebra.Recursion
