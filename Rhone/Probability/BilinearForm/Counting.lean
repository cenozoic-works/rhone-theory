/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Product

/-! # The `t = 2` combinatorics behind the level-function source -/

@[expose] public section

namespace Rhone.Probability.BilinearForm

open Finset LinearAlgebra.Recursion Config

variable {KA KB : ℕ} {F : Type*} [Field F]

theorem sum_mulPred_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℕ} (h : ∀ i, v i ≤ 1)
    (f : ι → F) : ∑ i, ((v i * (v i - 1) : ℕ) : F) * f i = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Denominator.mul_pred_eq_zero_of_le_one (h i)]
  simp

theorem sum_mulPred_eq_single {ι : Type*} [Fintype ι] {v : ι → ℕ} {i₀ : ι}
    (h0 : v i₀ = 2) (h : ∀ i, i ≠ i₀ → v i = 0) (f : ι → F) :
    ∑ i, ((v i * (v i - 1) : ℕ) : F) * f i = 2 * f i₀ := by
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
  · rw [h0]; norm_num
  · intro i _ hi; rw [h i hi]; simp

theorem cRow_eq_zero_of_ne {ξ : Config KA KB} (ht : ξ.t = 2) {i₀ : Fin KA} (h0 : ξ.cRow i₀ = 2)
    {i : Fin KA} (hi : i ≠ i₀) : ξ.cRow i = 0 := by
  have hsum : ∑ k, ξ.cRow k = 2 := by rw [← ξ.t_eq_sum_cRow, ht]
  have hle := pair_le_sum ξ.cRow (Ne.symm hi)
  omega

theorem cCol_eq_zero_of_ne {ξ : Config KA KB} (ht : ξ.t = 2) {j₀ : Fin KB} (h0 : ξ.cCol j₀ = 2)
    {j : Fin KB} (hj : j ≠ j₀) : ξ.cCol j = 0 := by
  have hsum : ∑ l, ξ.cCol l = 2 := by rw [← ξ.t_eq_sum_cCol, ht]
  have hle := pair_le_sum ξ.cCol (Ne.symm hj)
  omega

theorem two_mul_sumC_eq (ξ : Config KA KB) (ht : ξ.t = 2) (f : Fin KA → F) (g : Fin KB → F) :
    2 * ∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F) * (f i * g j)
      = (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * f i)
        * (∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * g j) := by
  by_cases hpair : ∃ (i₀ : Fin KA) (j₀ : Fin KB), ξ.c i₀ j₀ = 2
  · obtain ⟨i₀, j₀, h2⟩ := hpair
    have hrow0 : ξ.cRow i₀ = 2 := by
      have h1 : ξ.c i₀ j₀ ≤ ξ.cRow i₀ := le_cRow ξ i₀ j₀
      have h2' : ξ.cRow i₀ ≤ ξ.t := Denominator.cRow_le_t ξ i₀
      omega
    have hcol0 : ξ.cCol j₀ = 2 := by
      have h1 : ξ.c i₀ j₀ ≤ ξ.cCol j₀ := le_cCol ξ i₀ j₀
      have h2' : ξ.cCol j₀ ≤ ξ.t := Denominator.cCol_le_t ξ j₀
      omega
    have hrowz : ∀ i, i ≠ i₀ → ξ.cRow i = 0 := fun i hi => cRow_eq_zero_of_ne ht hrow0 hi
    have hcolz : ∀ j, j ≠ j₀ → ξ.cCol j = 0 := fun j hj => cCol_eq_zero_of_ne ht hcol0 hj
    have hcz : ∀ i j, ¬(i = i₀ ∧ j = j₀) → ξ.c i j = 0 := by
      intro i j hij
      by_cases hi : i = i₀
      · subst hi
        have hj : j ≠ j₀ := fun h => hij ⟨rfl, h⟩
        have := le_cCol ξ i j
        rw [hcolz j hj] at this
        omega
      · have := le_cRow ξ i j
        rw [hrowz i hi] at this
        omega
    have hinner : ∀ i : Fin KA,
        (∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F) * (f i * g j))
          = ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * (f i * g j₀) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        rw [hrow0, sum_mulPred_eq_single (v := ξ.c i) h2
          (fun j hj => hcz i j fun hij => hj hij.2) (fun j => f i * g j)]
        norm_num
      · rw [hrowz i hi]
        refine (Finset.sum_eq_zero fun j _ => ?_).trans (by norm_num)
        rw [hcz i j fun hij => hi hij.1]
        simp
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
      sum_mulPred_eq_single hrow0 hrowz (fun i => f i * g j₀),
      sum_mulPred_eq_single hcol0 hcolz g,
      sum_mulPred_eq_single hrow0 hrowz f]
    ring
  · simp only [not_exists] at hpair
    have hc1 : ∀ i j, ξ.c i j ≤ 1 := by
      intro i j
      have h1 : ξ.c i j ≤ ξ.cRow i := le_cRow ξ i j
      have h2 : ξ.cRow i ≤ ξ.t := Denominator.cRow_le_t ξ i
      have := hpair i j
      omega
    have hleft : (∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F) * (f i * g j)) = 0 :=
      Finset.sum_eq_zero fun i _ =>
        sum_mulPred_eq_zero (v := ξ.c i) (fun j => hc1 i j) (fun j => f i * g j)
    rw [hleft, mul_zero]
    by_cases hrow : ∃ i₀ : Fin KA, ξ.cRow i₀ = 2
    · obtain ⟨i₀, h0⟩ := hrow
      have hcolle : ∀ j, ξ.cCol j ≤ 1 := by
        intro j
        have hz : ∀ i, i ≠ i₀ → ξ.c i j = 0 := by
          intro i hi
          have := le_cRow ξ i j
          rw [cRow_eq_zero_of_ne ht h0 hi] at this
          omega
        have : ξ.cCol j = ξ.c i₀ j := by
          refine (Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀) ?_)
          intro i _ hi
          exact hz i hi
        rw [this]
        exact hc1 i₀ j
      rw [sum_mulPred_eq_zero hcolle g, mul_zero]
    · simp only [not_exists] at hrow
      have hrowle : ∀ i, ξ.cRow i ≤ 1 := by
        intro i
        have := Denominator.cRow_le_t ξ i
        have := hrow i
        omega
      rw [sum_mulPred_eq_zero hrowle f, zero_mul]

end Rhone.Probability.BilinearForm
