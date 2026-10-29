/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.SelectionGradient
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Genetic response in a finite independent genotype/environment model

Source: lande_arnold1983, p. 1212, eq. 5a, 6a. -/

@[expose] public section
namespace Rhone.Statistics
open Finset

/-- Source: lande_arnold1983, p. 1212, eq. 6a. -/
noncomputable def geneticCovariance {Γ κ : Type*} [Fintype Γ]
    (A : Γ → κ → ℝ) (j k : κ) : ℝ :=
  popCov (fun γ => A γ j) (fun γ => A γ k)

/-- Source: lande_arnold1983, p. 1212, eq. 5a. -/
noncomputable def genotypeEnvironmentPhenotype {Γ E κ : Type*}
    (A : Γ → κ → ℝ) (e : E → κ → ℝ) (pair : Γ × E) (j : κ) : ℝ :=
  A pair.1 j + e pair.2 j

/-- Source: lande_arnold1983, p. 1212, eq. 5a. -/
private theorem mean_product_first {Γ E : Type*}
    [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E] (f : Γ → ℝ) :
    popMean (fun p : Γ × E => f p.1) = popMean f := by
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  field_simp

/-- Source: lande_arnold1983, p. 1212, eq. 5a. -/
private theorem mean_product_second {Γ E : Type*}
    [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E] (g : E → ℝ) :
    popMean (fun p : Γ × E => g p.2) = popMean g := by
  have hg : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Source: lande_arnold1983, p. 1212, eq. 5a. -/
private theorem mean_product_mul {Γ E : Type*}
    [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E]
    (f : Γ → ℝ) (g : E → ℝ) :
    popMean (fun p : Γ × E => f p.1 * g p.2) = popMean f * popMean g := by
  simp only [popMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← mul_sum, ← sum_mul]
  ring

private theorem mean_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    popMean (fun i => c * f i) = c * popMean f := by
  simp only [popMean, ← Finset.mul_sum]
  ring

private theorem mean_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : κ → ι → ℝ) :
    popMean (fun i => ∑ k, f k i) = ∑ k, popMean (f k) := by
  simp only [popMean, Finset.sum_div]
  rw [Finset.sum_comm]

private theorem genetic_covariance_affine {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ι → ℝ) (c : ℝ) (b : κ → ℝ) :
    popCov f (fun i => c + ∑ k, b k * g k i) = ∑ k, b k * popCov f (g k) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hconst : popMean (fun _ : ι => c) = c := by simp [popMean, hc]
  simp only [popCov, mul_add, popMean_add, mean_sum]
  rw [hconst]
  have hprod : (fun i => f i * c) = (fun i => c * f i) := by funext i; ring
  rw [hprod, mean_mul]
  have hsum : (fun i => f i * ∑ k, b k * g k i) =
      (fun i => ∑ k, b k * (f i * g k i)) := by
    funext i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, mean_sum]
  simp only [mean_mul, Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem mean_div {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    popMean (fun i => f i / c) = popMean f / c := by
  simp only [popMean, ← Finset.sum_div]
  ring

/-- Source: lande_arnold1983, p. 1212, eq. 5a, 6a. -/
theorem genetic_phenotype_cross_covariance
    {Γ E κ : Type*} [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E]
    (A : Γ → κ → ℝ) (e : E → κ → ℝ) (j k : κ) :
    popCov (fun pair : Γ × E => A pair.1 j)
      (fun pair => genotypeEnvironmentPhenotype A e pair k) = geneticCovariance A j k := by
  unfold geneticCovariance
  simp only [popCov, genotypeEnvironmentPhenotype, mul_add, popMean_add]
  rw [mean_product_first (E := E) (fun γ => A γ j * A γ k),
    mean_product_mul (fun γ => A γ j) (fun ε => e ε k),
    mean_product_first (E := E) (fun γ => A γ j),
    mean_product_first (E := E) (fun γ => A γ k),
    mean_product_second (Γ := Γ) (fun ε => e ε k)]
  ring

/-- Source: lande_arnold1983, p. 1212, eq. 6a. -/
theorem genetic_response_lande
    {Γ E κ : Type*} [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E] [Fintype κ]
    (A : Γ → κ → ℝ) (e : E → κ → ℝ) (w : Γ × E → ℝ) (β : κ → ℝ)
    (hw0 : ∀ pair, 0 ≤ w pair) (hw : 0 < popMean w)
    (hfit : ∀ pair, w pair / popMean w = 1 +
      ∑ k, β k * (genotypeEnvironmentPhenotype A e pair k -
        popMean (fun pair => genotypeEnvironmentPhenotype A e pair k))) :
    ∀ j, selectionResponse w (fun pair => A pair.1 j) =
      ∑ k, geneticCovariance A j k * β k := by
  intro j
  have hmean0 : 0 ≤ popMean w := by
    exact div_nonneg (sum_nonneg fun i _ => hw0 i) (Nat.cast_nonneg _)
  have hwne := ne_of_gt (lt_of_le_of_ne hmean0 (Ne.symm (ne_of_gt hw)))
  have hrel : (fun pair => w pair / popMean w) =
      (fun pair => 1 - ∑ k, β k * popMean (fun pair => genotypeEnvironmentPhenotype A e pair k) +
        ∑ k, β k * genotypeEnvironmentPhenotype A e pair k) := by
    funext pair
    rw [hfit]
    simp only [mul_sub, sum_sub_distrib]
    ring
  have hcov : popCov (fun pair => A pair.1 j) (fun pair => w pair / popMean w) =
      ∑ k, β k * geneticCovariance A j k := by
    rw [hrel, genetic_covariance_affine]
    simp only [genetic_phenotype_cross_covariance]
  have hresp : selectionResponse w (fun pair => A pair.1 j) =
      popCov (fun pair => A pair.1 j) (fun pair => w pair / popMean w) := by
    unfold selectionResponse
    rw [robertson_price w _ hwne]
    conv_rhs => rw [popCov_comm]
    simp only [popCov, div_mul_eq_mul_div, mean_div]
    ring
  rw [hresp, hcov]
  exact sum_congr rfl fun k _ => mul_comm _ _

end Rhone.Statistics
