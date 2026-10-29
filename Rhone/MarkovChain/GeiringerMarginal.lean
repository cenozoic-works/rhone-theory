/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerModel

/-!
# Finite-mask recombination splits every marginal into two parental marginals

Source: geiringer1944, eq. (31), p. 39. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem recombination_expectation
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ) (f : (κ → Ω) → ℝ) :
    (∑ h, recombination ρ p h*f h) =
      ∑ mask, ρ mask*∑ parent, ∑ other,
        p parent*p other*f (assemble mask parent other) := by
  classical
  unfold recombination
  simp only [sum_mul, mul_assoc, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro mask _
  simp only [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro parent _
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro other _
  rw [← mul_sum]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

theorem assemble_matches_iff
    {κ Ω : Type*} [DecidableEq κ]
    (B mask : Finset κ) (parent other h : κ → Ω) :
    (∀ l ∈ B, assemble mask parent other l = h l) ↔
      (∀ l ∈ B ∩ mask, parent l = h l) ∧
      (∀ l ∈ B \ mask, other l = h l) := by
  constructor
  · intro hall
    constructor
    · intro l hl
      obtain ⟨hB, hm⟩ := mem_inter.mp hl
      simpa only [assemble, ite_eq_left hm] using hall l hB
    · intro l hl
      obtain ⟨hB, hm⟩ := mem_sdiff.mp hl
      simpa only [assemble, ite_eq_right hm] using hall l hB
  · rintro ⟨hfirst, hsecond⟩ l hl
    by_cases hm : l ∈ mask
    · simpa only [assemble, ite_eq_left hm] using hfirst l (mem_inter.mpr ⟨hl, hm⟩)
    · simpa only [assemble, ite_eq_right hm] using hsecond l (mem_sdiff.mpr ⟨hl, hm⟩)

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem marginal_recombination_split
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ) (B : Finset κ) (h : κ → Ω) :
    marginal (recombination ρ p) B h =
      ∑ mask, ρ mask*marginal p (B ∩ mask) h*marginal p (B \ mask) h := by
  classical
  unfold marginal
  rw [recombination_expectation]
  apply sum_congr rfl
  intro mask _
  simp_rw [assemble_matches_iff]
  rw [mul_assoc]
  congr 1
  rw [sum_mul]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro parent _
  apply sum_congr rfl
  intro other _
  split_ifs <;> simp_all

end Rhone.MarkovChain.Geiringer
