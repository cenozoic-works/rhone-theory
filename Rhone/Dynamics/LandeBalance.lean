/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
/-!
# Equilibrium of Lande's declared Gaussian covariance closure

Source: lande1975, p. 228, eq. 19–21c. -/
@[expose] public section
namespace Rhone.Dynamics.LandeBalance
open Finset

/-- Source: lande1975, p. 228, eq. 19–21c. -/
noncomputable def locusContribution {κ : Type*} [Fintype κ]
    (C : κ → κ → ℝ) (i : κ) : ℝ := ∑ j, C i j

/-- Source: lande1975, p. 228, eq. 19–21c. -/
noncomputable def geneticVariance {κ : Type*} [Fintype κ]
    (C : κ → κ → ℝ) : ℝ := 2*∑ i, locusContribution C i

/-- Source: lande1975, p. 228, eq. 19–21c. -/
noncomputable def covarianceStep {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : ℝ) (M : κ → ℝ) (r C : κ → κ → ℝ) (i j : κ) : ℝ :=
  C i j - locusContribution C i * locusContribution C j/(S + geneticVariance C) -
    r i j * C i j + if i=j then M i else 0

/-- Source: lande1975, p. 228, eq. 20. -/
private theorem variance_nonnegative {κ : Type*} [Fintype κ]
    (C : κ → κ → ℝ) (hR : ∀ i, 0 ≤ locusContribution C i) :
    0 ≤ geneticVariance C := by
  exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => hR i)

/-- Source: lande1975, p. 228, eq. 19. -/
private theorem effective_width_positive {κ : Type*} [Fintype κ]
    (S : ℝ) (C : κ → κ → ℝ) (hS : 0 < S)
    (hR : ∀ i, 0 ≤ locusContribution C i) :
    0 < S + geneticVariance C := by
  exact add_pos_of_pos_of_nonneg hS (variance_nonnegative C hR)

/-- Source: lande1975, p. 228, eq. 19–20. -/
private theorem equilibrium_locus_square {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : ℝ) (M : κ → ℝ) (r C : κ → κ → ℝ)
    (hS : 0 < S) (hrdiag : ∀ i, r i i = 0)
    (hR : ∀ i, 0 ≤ locusContribution C i)
    (heq : ∀ i j, covarianceStep S M r C i j = C i j) (i : κ) :
    (locusContribution C i) ^ 2 = M i * (S + geneticVariance C) := by
  have hd := effective_width_positive S C hS hR
  have hi := heq i i
  simp only [covarianceStep, hrdiag, zero_mul, sub_zero, ite_true] at hi
  have hdiv : locusContribution C i * locusContribution C i /
      (S + geneticVariance C) = M i := by linarith
  nlinarith [(div_eq_iff (ne_of_gt hd)).mp hdiv]

/-- Source: lande1975, p. 228, eq. 20. -/
private theorem equilibrium_locus_contribution {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (S : ℝ) (M : κ → ℝ) (r C : κ → κ → ℝ)
    (hS : 0 < S) (hM : ∀ i, 0 ≤ M i)
    (hrdiag : ∀ i, r i i = 0)
    (hR : ∀ i, 0 ≤ locusContribution C i)
    (heq : ∀ i j, covarianceStep S M r C i j = C i j) (i : κ) :
    locusContribution C i = Real.sqrt (M i) * Real.sqrt (S + geneticVariance C) := by
  have hi := equilibrium_locus_square S M r C hS hrdiag hR heq i
  have hd := effective_width_positive S C hS hR
  have hs := Real.sq_sqrt (hM i)
  have ht := Real.sq_sqrt (le_of_lt hd)
  have hp : 0 ≤ Real.sqrt (M i) * Real.sqrt (S + geneticVariance C) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he : (locusContribution C i) ^ 2 =
      (Real.sqrt (M i) * Real.sqrt (S + geneticVariance C)) ^ 2 := by
    rw [mul_pow, hs, ht, hi]
  nlinarith [hR i]

/-- Source: lande1975, p. 228, eq. 21c. -/
private theorem positive_quadratic_root (S L V : ℝ)
    (hS : 0 < S) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (heq : V ^ 2 = 4 * L ^ 2 * (S + V)) :
    V = 2 * L * Real.sqrt (S + L ^ 2) + 2 * L ^ 2 := by
  have hsq : 0 ≤ L ^ 2 := sq_nonneg L
  have hq := Real.sq_sqrt (le_of_lt (add_pos_of_pos_of_nonneg hS hsq))
  have hq0 := Real.sqrt_nonneg (S + L ^ 2)
  have hqL : L < Real.sqrt (S + L ^ 2) := by nlinarith
  have he : (V - 2 * L ^ 2) ^ 2 = (2 * L * Real.sqrt (S + L ^ 2)) ^ 2 := by
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp he) with h | h
  · linarith
  · by_cases hl : L = 0
    · subst L
      simp_all
    · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hl)
      have hp : 0 < L * (Real.sqrt (S + L ^ 2) - L) :=
        mul_pos hLpos (sub_pos.mpr hqL)
      nlinarith

/-- Source: lande1975, p. 228, eq. 21c. -/
theorem lande_equilibrium_total_variance
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : ℝ) (M : κ → ℝ) (r C : κ → κ → ℝ)
    (hS : 0 < S) (hM : ∀ i, 0 ≤ M i)
    (hrdiag : ∀ i, r i i = 0)
    (hR : ∀ i, 0 ≤ locusContribution C i)
    (heq : ∀ i j, covarianceStep S M r C i j = C i j) :
    geneticVariance C =
      2 * (∑ i, Real.sqrt (M i)) * Real.sqrt (S + (∑ i, Real.sqrt (M i)) ^ 2) +
      2 * (∑ i, Real.sqrt (M i)) ^ 2 := by
  let L : ℝ := ∑ i, Real.sqrt (M i)
  have hL : 0 ≤ L := sum_nonneg fun i _ => Real.sqrt_nonneg (M i)
  have hd := effective_width_positive S C hS hR
  have hsum : geneticVariance C = 2 * L * Real.sqrt (S + geneticVariance C) := by
    have hrow : (∑ i, locusContribution C i) = L * Real.sqrt (S + geneticVariance C) := by
      simp only [equilibrium_locus_contribution S M r C hS hM hrdiag hR heq,
        ← sum_mul]
      rfl
    change 2 * (∑ i, locusContribution C i) = _
    rw [hrow]
    ring
  have hquad : (geneticVariance C) ^ 2 = 4 * L ^ 2 * (S + geneticVariance C) := by
    conv_lhs => rw [hsum]
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hd)]
    ring
  exact positive_quadratic_root S L (geneticVariance C) hS hL
    (variance_nonnegative C hR) hquad

/-- Source: lande1975, p. 228, eq. 21a. -/
theorem lande_equilibrium_off_diagonal
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : ℝ) (M : κ → ℝ) (r C : κ → κ → ℝ)
    (hS : 0 < S) (hM : ∀ i, 0 ≤ M i)
    (hrdiag : ∀ i, r i i = 0)
    (hR : ∀ i, 0 ≤ locusContribution C i)
    (heq : ∀ i j, covarianceStep S M r C i j = C i j)
    (i j : κ) (hij : i ≠ j) (hrij : r i j ≠ 0) :
    C i j = -Real.sqrt (M i * M j)/r i j := by
  have hd := effective_width_positive S C hS hR
  have hi := heq i j
  simp only [covarianceStep, hij, ite_false, add_zero] at hi
  rw [equilibrium_locus_contribution S M r C hS hM hrdiag hR heq i,
    equilibrium_locus_contribution S M r C hS hM hrdiag hR heq j] at hi
  have hm : Real.sqrt (M i * M j) = Real.sqrt (M i) * Real.sqrt (M j) :=
    Real.sqrt_mul (hM i) (M j)
  rw [hm]
  apply (eq_div_iff hrij).mpr
  have ht := Real.sq_sqrt (le_of_lt hd)
  have hprod : Real.sqrt (M i) * Real.sqrt (S + geneticVariance C) *
      (Real.sqrt (M j) * Real.sqrt (S + geneticVariance C)) /
      (S + geneticVariance C) = Real.sqrt (M i) * Real.sqrt (M j) := by
    field_simp
    rw [ht]
  rw [hprod] at hi
  linarith

end Rhone.Dynamics.LandeBalance
