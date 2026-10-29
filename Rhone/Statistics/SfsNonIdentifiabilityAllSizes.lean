/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.SfsCoalescentTime
public import Rhone.Analysis.LaplaceNullFunction

/-!
# Two size histories with the same expected spectrum for every sample size

Source: myers_fefferman_patterson2008, secs. 3–5, eq. (20)–(24), Appendix Thm 1. -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory Coalescent Rhone.Combinatorics MarkovChain Analysis Probability
open scoped NNReal

/-- Source: myers_fefferman_patterson2008, secs. 3–5, eq. (24). -/
theorem exists_laplace_null_function :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∃ B : ℝ, ∀ τ, |G τ| ≤ B) ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Set.Ioo s t, G u ≠ 0) ∧
      ∀ k : ℕ, 2 ≤ k →
        ∫ τ in Set.Ioi 0, Real.exp (-(((coalRate k : ℚ) : ℝ) * τ)) * G τ = 0 := by
  refine ⟨laplaceNullFunction, continuous_laplaceNullFunction, bounded_laplaceNullFunction,
    exists_Ioo_laplaceNullFunction_ne_zero, fun k hk => ?_⟩
  have hc : ((coalRate k : ℚ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    simp [coalRate]
  rw [hc]
  exact integral_exp_mul_laplaceNullFunction k (by omega)

/-- Source: myers_fefferman_patterson2008, secs. 3–5, eq. (20)–(24), Appendix Thm 1. -/
theorem exists_size_ne_one_sfs_eq_constant_all_sizes {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ → ℝ, IsSizeFunction ν ∧ Continuous ν ∧ (∀ t, |ν t - 1| ≤ ε) ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Set.Ioo s t, ν u ≠ 1) ∧
      ∀ n i : ℕ, 1 ≤ i → i < n → ∀ θ : ℝ≥0,
        ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν θ = (θ : ℝ) / i := by
  obtain ⟨G, hG, ⟨B, hB⟩, hGne, hL⟩ := exists_laplace_null_function
  exact exists_size_ne_one_sfs_eq_constant_all_sizes_of_laplace hG hB hGne hL hε

/-- Source: myers_fefferman_patterson2008, secs. 3–5, eq. (20)–(24), Appendix Thm 1. -/
theorem exists_size_pair_same_sfs_all_sizes :
    ∃ ν₁ ν₂ : ℝ → ℝ, IsSizeFunction ν₁ ∧ IsSizeFunction ν₂ ∧ Continuous ν₁ ∧ Continuous ν₂ ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Set.Ioo s t, ν₁ u ≠ ν₂ u) ∧
      ∀ n i : ℕ, 1 ≤ i → i < n → ∀ θ : ℝ≥0,
        ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν₁ θ =
          ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν₂ θ := by
  obtain ⟨ν, hν, hc, -, hne, hsfs⟩ := exists_size_ne_one_sfs_eq_constant_all_sizes one_pos
  exact ⟨ν, fun _ => 1, hν, isSizeFunction_one, hc, continuous_const, hne,
    fun n i hi hin θ => by rw [hsfs n i hi hin θ, variableSizeMarkedLaw_one_sfs_mean hi hin θ]⟩

end Rhone.Statistics
