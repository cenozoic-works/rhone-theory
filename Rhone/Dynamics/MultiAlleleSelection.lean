/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.HaploidSelection
public import Rhone.Dynamics.DiploidSelection
public import Rhone.Dynamics.MultiAlleleInequality
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Diploid viability selection at a multiallelic locus

Source: kingman1961_partial_averages, eq. (1), p. 78; burger2013_migration_selection, sec. 2.2, eq.
(2.13). -/

@[expose] public section

namespace Rhone.Dynamics

variable {ι : Type*} [Fintype ι]

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
noncomputable def marginalFit (W : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, W i j * p j

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
noncomputable def multiMeanFit (W : ι → ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, p i * marginalFit W p i

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
noncomputable def multiSelStep (W : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  p i * marginalFit W p i / multiMeanFit W p

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
theorem marginalFit_nonneg (W : ι → ι → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hW : ∀ i j, 0 ≤ W i j) (i : ι) :
    0 ≤ marginalFit W p i := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hW i j) (hp j)

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
theorem multiMeanFit_eq_sum (W : ι → ι → ℝ) (p : ι → ℝ) :
    multiMeanFit W p = ∑ i, ∑ j, p i * p j * W i j := by
  simp only [multiMeanFit, marginalFit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Source: burger2013_migration_selection, sec. 2.2, eq. 2.4–2.6. -/
theorem multiSelStep_simplex (W : ι → ι → ℝ) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (_hp1 : ∑ i, p i = 1)
    (_hsym : ∀ i j, W i j = W j i) (hW0 : ∀ i j, 0 ≤ W i j)
    (hbar : 0 < multiMeanFit W p) :
    (∀ i, 0 ≤ multiSelStep W p i) ∧ ∑ i, multiSelStep W p i = 1 := by
  refine ⟨fun i => div_nonneg
    (mul_nonneg (hp0 i) (marginalFit_nonneg W p hp0 hW0 i)) hbar.le, ?_⟩
  change (∑ i, p i * marginalFit W p i / multiMeanFit W p) = 1
  rw [← Finset.sum_div]
  change multiMeanFit W p / multiMeanFit W p = 1
  exact div_self hbar.ne'

/-- Source: crow_kimura1970, sec. 6.2. -/
def twoFreq (p : ℝ) : Fin 2 → ℝ := ![p, 1 - p]

/-- Source: crow_kimura1970, sec. 6.2. -/
def twoFitness (w11 w12 w22 : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![w11, w12], ![w12, w22]]

/-- Source: crow_kimura1970, sec. 6.2. -/
theorem multiMeanFit_two (w11 w12 w22 p : ℝ) :
    multiMeanFit (twoFitness w11 w12 w22) (twoFreq p) = meanFit w11 w12 w22 p := by
  simp [multiMeanFit, marginalFit, twoFitness, twoFreq, Fin.sum_univ_two, meanFit]
  ring

/-- Source: crow_kimura1970, sec. 6.2, eq. 6.2.2. -/
theorem multiSelStep_two (w11 w12 w22 p : ℝ) :
    multiSelStep (twoFitness w11 w12 w22) (twoFreq p) 0 = selStep w11 w12 w22 p := by
  rw [multiSelStep, multiMeanFit_two]
  simp only [marginalFit, Fin.sum_univ_two,
    twoFitness, twoFreq, Matrix.cons_val_zero, Matrix.cons_val_one, selStep]
  congr 1
  ring

theorem multiMeanFit_entropy_bound (W : ι → ι → ℝ) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hsym : ∀ i j, W i j = W j i) (hW0 : ∀ i j, 0 ≤ W i j)
    (hbar : 0 < multiMeanFit W p) :
    1 + 2 * (∑ i, p i * selectionEntropyGap
      (marginalFit W p i / multiMeanFit W p)) ≤
      multiMeanFit W (multiSelStep W p) / multiMeanFit W p := by
  let b := multiMeanFit W p
  let r : ι → ℝ := fun i => marginalFit W p i / b
  let a : ι → ι → ℝ := fun i j => p i * p j * W i j / b
  have hr : ∀ i, 0 ≤ r i := fun i =>
    div_nonneg (marginalFit_nonneg W p hp0 hW0 i) hbar.le
  have ha : ∀ i j, 0 ≤ a i j := fun i j =>
    div_nonneg (mul_nonneg (mul_nonneg (hp0 i) (hp0 j)) (hW0 i j)) hbar.le
  have hasym : ∀ i j, a i j = a j i := by
    intro i j
    dsimp [a]
    rw [hsym i j]
    ring
  have hrow : ∀ i, ∑ j, a i j = p i * r i := by
    intro i
    dsimp [a, r, marginalFit]
    rw [← Finset.sum_div, ← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr1 : ∑ i, p i * r i = 1 := by
    simp only [r, ← mul_div_assoc, ← Finset.sum_div]
    change b / b = 1
    exact div_self hbar.ne'
  have hnext : (∑ i, ∑ j, a i j * r i * r j) =
      multiMeanFit W (multiSelStep W p) / b := by
    rw [multiMeanFit_eq_sum]
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a, r, multiSelStep, b]
    ring
  have hbound := selection_edge_entropy_bound p r a hp0 hr ha hasym hp1 hrow hr1
  rw [hnext] at hbound
  exact hbound

/--
Source: kingman1961_partial_averages, eq. (1), p. 78; burger2013_migration_selection, sec. 2.2, eq.
(2.13). -/
theorem multiMeanFit_mono (W : ι → ι → ℝ) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hsym : ∀ i j, W i j = W j i) (hW0 : ∀ i j, 0 ≤ W i j)
    (hbar : 0 < multiMeanFit W p) :
    multiMeanFit W p ≤ multiMeanFit W (multiSelStep W p) := by
  have hbound := multiMeanFit_entropy_bound W p hp0 hp1 hsym hW0 hbar
  have hgap : 0 ≤ ∑ i, p i * selectionEntropyGap
      (marginalFit W p i / multiMeanFit W p) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i)
      (selectionEntropyGap_nonneg
        (div_nonneg (marginalFit_nonneg W p hp0 hW0 i) hbar.le))
  have hratio : 1 ≤ multiMeanFit W (multiSelStep W p) / multiMeanFit W p := by
    linarith
  simpa using (le_div_iff₀ hbar).mp hratio

/--
Source: kingman1961_partial_averages, p. 79; burger2013_migration_selection, sec. 2.2, eq. (2.13).
-/
theorem multiMeanFit_eq_iff_fixed (W : ι → ι → ℝ) (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hsym : ∀ i j, W i j = W j i) (hW0 : ∀ i j, 0 ≤ W i j)
    (hbar : 0 < multiMeanFit W p) :
    multiMeanFit W (multiSelStep W p) = multiMeanFit W p ↔ multiSelStep W p = p := by
  constructor
  · intro heq
    let r : ι → ℝ := fun i => marginalFit W p i / multiMeanFit W p
    have hr : ∀ i, 0 ≤ r i := fun i =>
      div_nonneg (marginalFit_nonneg W p hp0 hW0 i) hbar.le
    have hgap : (∑ i, p i * selectionEntropyGap (r i)) = 0 := by
      have hbound := multiMeanFit_entropy_bound W p hp0 hp1 hsym hW0 hbar
      rw [heq, div_self hbar.ne'] at hbound
      have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
        mul_nonneg (hp0 i) (selectionEntropyGap_nonneg (hr i)))
      change 1 + 2 * (∑ i, p i * selectionEntropyGap (r i)) ≤ 1 at hbound
      linarith
    have hs := (selection_entropy_sum_eq_zero_iff p r hp0 hr).mp hgap
    funext i
    rcases hs i with hi | hi
    · simp [multiSelStep, hi]
    · change p i * marginalFit W p i / multiMeanFit W p = p i
      rw [mul_div_assoc]
      change p i * r i = p i
      rw [hi, mul_one]
  · intro hfix
    rw [hfix]

end Rhone.Dynamics
