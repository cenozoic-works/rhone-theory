/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GeneticResponse
public import Mathlib.Algebra.BigOperators.Fin
/-!
# Finite Mendelian mating and complete haplotype segregation law

Source: lande_arnold1983, p. 1212, eq. 6b. -/
@[expose] public section
namespace Rhone.Statistics
open Finset

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
noncomputable def diploidGeneticTrait {Γ L κ : Type*} [Fintype L]
    (a : Γ → Fin 2 → L → κ → ℝ) (γ : Γ) (j : κ) : ℝ :=
  ∑ l, (a γ 0 l j + a γ 1 l j)

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
noncomputable def selectedParentProbability {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (i : ι) : ℝ := w i / ∑ k, w k

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
noncomputable def mendelianOffspringMean {Γ E L κ : Type*}
    [Fintype Γ] [Fintype E] [Fintype L]
    (a : Γ → Fin 2 → L → κ → ℝ) (w : Γ × E → ℝ) (j : κ) : ℝ :=
  ∑ p, ∑ q, selectedParentProbability w p * selectedParentProbability w q *
    popMean (fun slots : Fin 2 × Fin 2 =>
      ∑ l, (a p.1 slots.1 l j + a q.1 slots.2 l j))

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
private theorem selected_parent_nonnegative {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ p, 0 ≤ w p) (i : ι) :
    0 ≤ selectedParentProbability w i := by
  exact div_nonneg (hw0 i) (sum_nonneg fun p _ => hw0 p)

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
private theorem selected_parent_normalized {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : 0 < popMean w) :
    ∑ i, selectedParentProbability w i = 1 := by
  have hs : (∑ i, w i) ≠ 0 := by
    intro h
    have : popMean w = 0 := by simp [popMean, h]
    exact (ne_of_gt hw) this
  simp only [selectedParentProbability, ← sum_div]
  exact div_self hs

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
private theorem segregation_mean {Γ L κ : Type*} [Fintype L]
    (a : Γ → Fin 2 → L → κ → ℝ) (p q : Γ) (j : κ) :
    popMean (fun slots : Fin 2 × Fin 2 =>
      ∑ l, (a p slots.1 l j + a q slots.2 l j)) =
      (diploidGeneticTrait a p j + diploidGeneticTrait a q j) / 2 := by
  simp only [popMean, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.card_prod,
    Fintype.card_fin, diploidGeneticTrait, sum_add_distrib]
  norm_num
  ring

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
private theorem random_mating_mean {ι : Type*} [Fintype ι]
    (r f : ι → ℝ) (hr : ∑ i, r i = 1) :
    (∑ p, ∑ q, r p * r q * ((f p + f q) / 2)) = ∑ p, r p * f p := by
  have hterm (p q : ι) : r p * r q * ((f p + f q) / 2) =
      (r p * f p) * r q / 2 + r p * (r q * f q) / 2 := by ring
  simp only [hterm, sum_add_distrib, ← sum_div, ← mul_sum, ← sum_mul, hr]
  ring

/-- Source: lande_arnold1983, p. 1212, eq. 5a, 6b. -/
private theorem product_environment_mean {Γ E : Type*}
    [Fintype Γ] [Nonempty Γ] [Fintype E] [Nonempty E]
    (f : Γ → ℝ) (g : E → ℝ) :
    popMean (fun p : Γ × E => f p.1 + g p.2) = popMean f + popMean g := by
  have hg : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [popMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  field_simp

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
theorem mendelian_offspring_genetic_mean
    {Γ E L κ : Type*} [Fintype Γ] [Nonempty Γ]
    [Fintype E] [Nonempty E] [Fintype L]
    (a : Γ → Fin 2 → L → κ → ℝ) (w : Γ × E → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : 0 < popMean w) (j : κ) :
    mendelianOffspringMean a w j =
      nextMean w (fun p => diploidGeneticTrait a p.1 j) := by
  have hp : ∑ p, selectedParentProbability w p = 1 := selected_parent_normalized w hw
  have hp0 := selected_parent_nonnegative w hw0
  have hmass0 : 0 ≤ ∑ p, selectedParentProbability w p := sum_nonneg fun p _ => hp0 p
  have hmass : 0 < ∑ p, selectedParentProbability w p :=
    lt_of_le_of_ne hmass0 (by rw [hp]; norm_num)
  have hs : (∑ p, w p) ≠ 0 := by
    intro h
    have : (∑ p, selectedParentProbability w p) = 0 := by
      simp [selectedParentProbability, h]
    exact (ne_of_gt hmass) this
  unfold mendelianOffspringMean
  simp only [segregation_mean]
  rw [random_mating_mean _ _ hp]
  simp only [selectedParentProbability, nextMean, popMean, div_mul_eq_mul_div, ← sum_div]
  have hc : (Fintype.card (Γ × E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Source: lande_arnold1983, p. 1212, eq. 6b. -/
theorem mendelian_phenotype_response_lande
    {Γ E L κ : Type*} [Fintype Γ] [Nonempty Γ]
    [Fintype E] [Nonempty E] [Fintype L] [Fintype κ]
    (a : Γ → Fin 2 → L → κ → ℝ) (e : E → κ → ℝ)
    (w : Γ × E → ℝ) (β : κ → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : 0 < popMean w)
    (hfit : ∀ p, w p / popMean w = 1 + ∑ k, β k *
      (genotypeEnvironmentPhenotype (diploidGeneticTrait a) e p k -
        popMean (fun p => genotypeEnvironmentPhenotype (diploidGeneticTrait a) e p k))) :
    ∀ j, mendelianOffspringMean a w j + popMean (fun ε => e ε j) -
      popMean (fun p => genotypeEnvironmentPhenotype (diploidGeneticTrait a) e p j) =
      ∑ k, geneticCovariance (diploidGeneticTrait a) j k * β k := by
  intro j
  rw [mendelian_offspring_genetic_mean a w hw0 hw j]
  unfold genotypeEnvironmentPhenotype
  rw [product_environment_mean (fun γ => diploidGeneticTrait a γ j) (fun ε => e ε j)]
  have h := genetic_response_lande (diploidGeneticTrait a) e w β hw0 hw hfit j
  unfold selectionResponse at h
  have ha : popMean (fun p : Γ × E => diploidGeneticTrait a p.1 j) =
      popMean (fun γ => diploidGeneticTrait a γ j) := by
    simpa [popMean] using
      product_environment_mean (fun γ => diploidGeneticTrait a γ j) (fun _ : E => (0 : ℝ))
  rw [ha] at h
  convert h using 1
  ring

end Rhone.Statistics
