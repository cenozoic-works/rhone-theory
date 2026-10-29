/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FisherLeastSquares
public import Mathlib.Data.Fintype.Sigma

/-!
# Whole-genome Fisher partial change with least-squares effects

Source: ewens_lessard2015, p. 61, eq. 11–13; ewens1989, pp. 175–177, eq. (22)–(28). -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {G K : Type*} [Fintype G]

/-- Source: ewens_lessard2015, p. 61. -/
noncomputable def fisherAlleleFreq [Fintype K]
    (P : G → ℝ) (X : G → K → ℝ) (k : K) : ℝ :=
  wMean P (fun g => X g k) / 2

variable [Fintype K]

/-- Source: ewens_lessard2015, p. 61. -/
noncomputable def fisherSelectedAlleleFreq
    (P W : G → ℝ) (X : G → K → ℝ) (k : K) : ℝ :=
  fisherAlleleFreq (haploidStep P W) X k

/-- Source: ewens_lessard2015, p. 61, eq. 13. -/
noncomputable def fisherAdditiveVar
    (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  wMean P (fun g => (fisherScore X β g - wMean P W) ^ 2)

/-- Source: ewens_lessard2015, p. 61, eq. 11–13. -/
noncomputable def fisherPartial
    (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  2 * ∑ k, (fisherSelectedAlleleFreq P W X k - fisherAlleleFreq P X k) * β k

/-- Source: ewens_lessard2015, p. 61. -/
theorem fisher_selected_allele_formula
    (P W : G → ℝ) (X : G → K → ℝ) (k : K) :
    fisherSelectedAlleleFreq P W X k =
      wMean P (fun g => W g * X g k) / (2 * wMean P W) := by
  unfold fisherSelectedAlleleFreq fisherAlleleFreq haploidStep wMean
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  ring

section Copycounts
variable {L : Type*} {A : L → Type*} [∀ l, Fintype (A l)]

/-- Source: ewens_lessard2015, p. 61. -/
theorem fisher_allele_freq_simplex [Fintype L]
    (P : G → ℝ) (X : G → (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2) (l : L) :
    (∀ a, 0 ≤ fisherAlleleFreq P X ⟨l, a⟩) ∧
      ∑ a, fisherAlleleFreq P X ⟨l, a⟩ = 1 := by
  refine ⟨fun a => div_nonneg
    (Finset.sum_nonneg fun g _ => mul_nonneg (hp0 g) (hX0 g _)) (by norm_num), ?_⟩
  unfold fisherAlleleFreq wMean
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcopies]
  rw [← Finset.sum_mul, hp1]
  norm_num

/-- Source: ewens_lessard2015, p. 61. -/
theorem fisher_selected_allele_simplex [Fintype L]
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hW0 : ∀ g, 0 ≤ W g)
    (hbar : 0 < wMean P W) (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2) (l : L) :
    (∀ a, 0 ≤ fisherSelectedAlleleFreq P W X ⟨l, a⟩) ∧
      ∑ a, fisherSelectedAlleleFreq P W X ⟨l, a⟩ = 1 := by
  exact fisher_allele_freq_simplex (haploidStep P W) X
    (haploidStep_nonneg P W hp0 hW0 hbar)
    (haploidStep_sum_eq_one P W hbar.ne') hX0 hcopies l

variable [Fintype L] [Nonempty L]

/-- Source: ewens1989, p. 171; ewens_lessard2015, p. 61. -/
theorem fisher_fitted_mean
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (_hp1 : ∑ g, P g = 1)
    (_hW0 : ∀ g, 0 ≤ W g) (_hbar : 0 < wMean P W)
    (_hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) :
    wMean P (fisherScore X β) = wMean P W := by
  classical
  let l : L := Classical.arbitrary L
  have hn : (∑ a : A l, wMean P (fun g =>
      (W g - fisherScore X β g) * X g ⟨l, a⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact fisher_leastSquares_normal P W X β hp0 hfit ⟨l, a⟩
  unfold wMean at hn ⊢
  rw [Finset.sum_comm] at hn
  simp_rw [← mul_assoc, ← Finset.mul_sum, hcopies] at hn
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hn
  linarith

/-- Source: ewens_lessard2015, p. 61, eq. 11–13; ewens1989, pp. 176–177, eq. (26)–(28). -/
theorem fisher_fundamental_theorem
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hW0 : ∀ g, 0 ≤ W g) (hbar : 0 < wMean P W)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) :
    fisherPartial P W X β = fisherAdditiveVar P W X β / wMean P W := by
  have hmean := fisher_fitted_mean P W X β hp0 hp1 hW0 hbar hX0 hcopies hfit
  have hnormal : wMean P (fun g =>
      (W g - fisherScore X β g) * fisherScore X β g) = 0 := by
    calc
      _ = ∑ k, wMean P (fun g =>
          (W g - fisherScore X β g) * X g k) * β k := by
        unfold wMean
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        change P g * ((W g - fisherScore X β g) * (∑ k, X g k * β k)) = _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by
        simp only [fisher_leastSquares_normal P W X β hp0 hfit,
          zero_mul, Finset.sum_const_zero]
  have hcross : wMean P (fun g => W g * fisherScore X β g) =
      wMean P (fun g => fisherScore X β g * fisherScore X β g) := by
    unfold wMean at hnormal ⊢
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib] at hnormal
    linarith
  have hcov : wCov P W (fisherScore X β) = wVar P (fisherScore X β) := by
    rw [wCov, wVar, wCov, hcross, hmean]
  have hvar : wVar P (fisherScore X β) = fisherAdditiveVar P W X β := by
    rw [wVar_eq_mean_sq_sub P (fisherScore X β) hp1, hmean]
    rfl
  have houtput (Q : G → ℝ) :
      2 * (∑ k, fisherAlleleFreq Q X k * β k) = wMean Q (fisherScore X β) := by
    unfold fisherAlleleFreq wMean fisherScore
    calc
      _ = ∑ k, ∑ g, Q g * (X g k * β k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have hm : (∑ g, Q g * (X g k * β k)) =
            (∑ g, Q g * X g k) * β k := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro g _
          ring
        rw [hm]
        ring
      _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  have hpartial : fisherPartial P W X β =
      wMean (haploidStep P W) (fisherScore X β) - wMean P (fisherScore X β) := by
    unfold fisherPartial fisherSelectedAlleleFreq
    simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
    rw [houtput, houtput]
  rw [hpartial, haploid_traitMean_change P W (fisherScore X β) hbar.ne', hcov, hvar]

/-- Source: ewens_lessard2015, p. 61, eq. 13. -/
theorem fisher_partial_nonneg
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hW0 : ∀ g, 0 ≤ W g) (hbar : 0 < wMean P W)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) : 0 ≤ fisherPartial P W X β := by
  rw [fisher_fundamental_theorem P W X β hp0 hp1 hW0 hbar hX0 hcopies hfit]
  exact div_nonneg (Finset.sum_nonneg fun g _ =>
    mul_nonneg (hp0 g) (sq_nonneg _)) hbar.le

end Copycounts
end Rhone.Statistics
