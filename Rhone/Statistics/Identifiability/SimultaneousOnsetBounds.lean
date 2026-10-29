/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetCertificates
public import Rhone.Statistics.Identifiability.TimeOrderedRemainder

/-! # Common contractive bounds for the product generator at simultaneous onset -/

@[expose] public section

open Set
open scoped BigOperators Matrix Matrix.Norms.Operator
open Rhone.MarkovChain.Identifiability Rhone.Statistics.Identifiability

namespace Rhone.Statistics.Identifiability.SimultaneousOnset

theorem productGenerator_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    ∀ i j, Continuous (fun t => productGenerator k (c t) (q t) (r t) i j) := by
  intro ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    dsimp [productGenerator, generator, pairGenerator, totalMigration] <;> fun_prop

theorem productGenerator_metzler (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ∀ i j : ProductState, i ≠ j → 0 ≤ productGenerator k c q r i j := by
  intro i j hij
  by_cases hp : i.1 = j.1
  · have ha : i.2 ≠ j.2 := fun ha => hij (Prod.ext hp ha)
    simpa [productGenerator, hp, ha] using pairGenerator_metzler k hq i.2 j.2 ha
  · by_cases ha : i.2 = j.2
    · simpa [productGenerator, hp, ha] using generator_metzler k hc hq hr i.1 j.1 hp
    · simp [productGenerator, hp, ha]

theorem pairGenerator_row_sum_local (k : ℕ) (c q : ℝ) (i : Fin 2) :
    (∑ j, pairGenerator k c q i j) = if i = 0 then -c else 0 := by
  fin_cases i <;> simp [pairGenerator, Fin.sum_univ_two]

theorem productGenerator_row_sum (k : ℕ) (c q r : ℝ) (i : ProductState) :
    (∑ j, productGenerator k c q r i j) =
      -c * (killedCount (shape i.1) : ℝ) + (if i.2 = 0 then -c else 0) := by
  have h := productGenerator_mulVec k c q r (fun _ => 1) i.1 i.2
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [generator_row_sum, pairGenerator_row_sum_local] at h
  exact h

theorem productGenerator_rows_nonpos (k : ℕ) {c q r : ℝ} (hc : 0 ≤ c)
    (i : ProductState) : (∑ j, productGenerator k c q r i j) ≤ 0 := by
  rw [productGenerator_row_sum]
  apply add_nonpos
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Nat.cast_nonneg _)
  · split_ifs <;> linarith

theorem exists_productGenerator_contractiveBound (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) :
    ∃ K : ℝ, 0 ≤ K ∧
      HasContractiveBoundOn (fun t => productGenerator k (c t) (q t) (r t)) 0 1 K := by
  have hcont := productGenerator_continuous k c q r hc hq hr
  have hmatrix : Continuous (fun t => productGenerator k (c t) (q t) (r t)) :=
    continuous_pi fun i => continuous_pi (hcont i)
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hmatrix.continuousOn
    (s := Icc (0 : ℝ) 1)
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  apply hasContractiveBoundOn_of_subgenerator _ hcont
    (fun t ht => productGenerator_metzler k (hcn t ht) (hqn t ht) (hrn t ht))
    (fun t ht i => productGenerator_rows_nonpos k (hcn t ht) i) (by norm_num)
  intro t ht
  exact (hL t ht).trans (le_max_left _ _)

theorem contractiveBoundOn_mono_budget
    {Q : ℝ → Matrix ProductState ProductState ℝ} {s t K L : ℝ}
    (h : HasContractiveBoundOn Q s t K) (hKL : K ≤ L) :
    HasContractiveBoundOn Q s t L :=
  ⟨fun u hu => (h.1 u hu).trans hKL, h.2⟩

theorem exists_common_contractiveBound (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) :
    ∃ K : ℝ, 0 ≤ K ∧
      HasContractiveBoundOn (fun t => productGenerator k (c t) 0 0) 0 1 K ∧
      HasContractiveBoundOn (fun t => productGenerator k (c t) (q t) 0) 0 1 K ∧
      HasContractiveBoundOn (fun t => productGenerator k (c t) 0 (r t)) 0 1 K ∧
      HasContractiveBoundOn (fun t => productGenerator k (c t) (q t) (r t)) 0 1 K := by
  obtain ⟨K₀, hK₀, h₀⟩ := exists_productGenerator_contractiveBound k c (fun _ => 0)
    (fun _ => 0) hc continuous_const continuous_const hcn (by simp) (by simp)
  obtain ⟨K₁, _, h₁⟩ := exists_productGenerator_contractiveBound k c q
    (fun _ => 0) hc hq continuous_const hcn hqn (by simp)
  obtain ⟨K₂, _, h₂⟩ := exists_productGenerator_contractiveBound k c
    (fun _ => 0) r hc continuous_const hr hcn (by simp) hrn
  obtain ⟨K₃, _, h₃⟩ := exists_productGenerator_contractiveBound k c q r
    hc hq hr hcn hqn hrn
  let K := max (max K₀ K₁) (max K₂ K₃)
  have h₀K : K₀ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have h₁K : K₁ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have h₂K : K₂ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have h₃K : K₃ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨K, hK₀.trans h₀K, contractiveBoundOn_mono_budget h₀ h₀K,
    contractiveBoundOn_mono_budget h₁ h₁K, contractiveBoundOn_mono_budget h₂ h₂K,
    contractiveBoundOn_mono_budget h₃ h₃K⟩

end Rhone.Statistics.Identifiability.SimultaneousOnset
