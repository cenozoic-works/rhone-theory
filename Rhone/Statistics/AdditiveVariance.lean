/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

public import Rhone.Statistics.Price
public import Mathlib.Data.Fintype.Prod

/-!
# Additive score variance under random union of haplotypes

Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/

@[expose] public section

namespace Rhone.Statistics

/-- Source: bulmer1971, eq. (3), p. 201; bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def diploidAdditiveScore {H κ : Type*} [Fintype κ]
    (α : κ → ℝ) (x : H → κ → ℝ) (pair : H × H) : ℝ :=
  ∑ j, α j * (x pair.1 j + x pair.2 j)

/-- Source: bulmer1971, eq. (9), p. 203; bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def gameticDisequilibrium {H κ : Type*} [Fintype H]
    (x : H → κ → ℝ) (j k : κ) : ℝ :=
  popCov (fun h => x h j) (fun h => x h k)

private theorem mean_linear {H κ : Type*} [Fintype H] [Fintype κ]
    (a : κ → ℝ) (f : κ → H → ℝ) :
    popMean (fun h => ∑ j, a j * f j h) = ∑ j, a j * popMean (f j) := by
  simp only [popMean, Finset.sum_div, mul_div_assoc]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

private theorem variance_linear {H κ : Type*} [Fintype H] [Fintype κ]
    (a : κ → ℝ) (f : κ → H → ℝ) :
    popCov (fun h => ∑ j, a j * f j h) (fun h => ∑ j, a j * f j h) =
      ∑ j, ∑ k, a j * a k * popCov (f j) (f k) := by
  simp only [popCov, mean_linear]
  have hprod : (fun h => (∑ j, a j * f j h) * ∑ k, a k * f k h) =
      (fun h => ∑ j, ∑ k, (a j * a k) * (f j h * f k h)) := by
    funext h
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hprod]
  have hmean : popMean (fun h => ∑ j, ∑ k, (a j * a k) * (f j h * f k h)) =
      ∑ j, ∑ k, (a j * a k) * popMean (fun h => f j h * f k h) := by
    simp only [popMean, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, mul_div_assoc]
  rw [hmean, Finset.sum_mul]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem mean_product {H : Type*} [Fintype H] [Nonempty H]
    (f g : H → ℝ) :
    popMean (fun pair : H × H => f pair.1 * g pair.2) = popMean f * popMean g := by
  have hc : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp

private theorem mean_first {H : Type*} [Fintype H] [Nonempty H] (f : H → ℝ) :
    popMean (fun pair : H × H => f pair.1) = popMean f := by
  have hc : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

private theorem mean_second {H : Type*} [Fintype H] [Nonempty H] (f : H → ℝ) :
    popMean (fun pair : H × H => f pair.2) = popMean f := by
  have hc : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private theorem cov_diploid {H : Type*} [Fintype H] [Nonempty H] (f g : H → ℝ) :
    popCov (fun pair : H × H => f pair.1 + f pair.2)
      (fun pair : H × H => g pair.1 + g pair.2) = 2 * popCov f g := by
  have hprod : (fun pair : H × H =>
      (f pair.1 + f pair.2) * (g pair.1 + g pair.2)) =
      (fun pair => (f pair.1 * g pair.1 + f pair.1 * g pair.2) +
        (g pair.1 * f pair.2 + f pair.2 * g pair.2)) := by
    funext pair
    ring
  simp only [popCov, popMean_add]
  rw [hprod]
  simp only [popMean_add, mean_product, mean_first, mean_second]
  rw [mean_first (fun h => f h * g h), mean_second (fun h => f h * g h)]
  ring

private theorem cov_binary {H : Type*} [Fintype H] (f : H → ℝ)
    (hb : ∀ h, f h = 0 ∨ f h = 1) :
    popCov f f = popMean f * (1 - popMean f) := by
  have heq : (fun h => f h * f h) = f := by
    funext h
    rcases hb h with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [popCov, heq]
  ring

/-- Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/
theorem additive_variance_ld_decomposition
    {H κ : Type*} [Fintype H] [Nonempty H] [Fintype κ] [DecidableEq κ]
    (α : κ → ℝ) (x : H → κ → ℝ)
    (hbinary : ∀ h j, x h j = 0 ∨ x h j = 1) :
    popCov (diploidAdditiveScore α x) (diploidAdditiveScore α x) =
      2 * (∑ j, α j ^ 2 * popMean (fun h => x h j) *
        (1 - popMean (fun h => x h j))) +
      2 * (∑ j, ∑ k ∈ Finset.univ.erase j,
        α j * α k * gameticDisequilibrium x j k) := by
  unfold diploidAdditiveScore
  rw [variance_linear]
  have hcov (j k : κ) :
      popCov (fun pair : H × H => x pair.1 j + x pair.2 j)
        (fun pair : H × H => x pair.1 k + x pair.2 k) =
        2 * popCov (fun h => x h j) (fun h => x h k) :=
    cov_diploid (fun h => x h j) (fun h => x h k)
  simp_rw [hcov]
  have hsplit : (∑ j, ∑ k, α j * α k * popCov (fun h => x h j) (fun h => x h k)) =
      (∑ j, α j ^ 2 * popMean (fun h => x h j) * (1 - popMean (fun h => x h j))) +
      ∑ j, ∑ k ∈ Finset.univ.erase j, α j * α k * gameticDisequilibrium x j k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    rw [cov_binary (fun h => x h j) (fun h => hbinary h j)]
    simp only [gameticDisequilibrium]
    ring
  have hfactor : (∑ j, ∑ k, α j * α k * (2 * popCov (fun h => x h j) (fun h => x h k))) =
      2 * ∑ j, ∑ k, α j * α k * popCov (fun h => x h j) (fun h => x h k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfactor, hsplit]
  ring

end Rhone.Statistics
