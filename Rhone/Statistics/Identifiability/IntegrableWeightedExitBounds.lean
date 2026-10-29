/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableWeightedExit
public import Rhone.Statistics.Identifiability.IntegrableDiagonalLowerBound
public import Rhone.Statistics.Identifiability.ACFluxMassBound
public import Rhone.Statistics.Identifiability.ExitCDF

/-! # Positivity, subprobability, and observed CDFs for locally-L1 weighted exit laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix ENNReal
namespace Rhone.Statistics.Identifiability.IntegrableWeightedExit
variable {n : ℕ}

lemma row_nonnegative (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j) (hα : ∀ i, 0 ≤ α i)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (j : Fin n) : 0 ≤ row Q α a t j := by
  unfold row Matrix.vecMul dotProduct
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hα i)
    (integrableTransition_nonneg Q hQ hn ha hat i j)

lemma survival_nonnegative (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j) (hα : ∀ i, 0 ≤ α i)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) : 0 ≤ survival Q α a t :=
  Finset.sum_nonneg fun j _ => row_nonnegative Q α hQ hn hα ha hat j

lemma survival_positive (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) : 0 < survival Q α a t := by
  have hex : ∃ i, 0 < α i := by
    by_contra h
    push Not at h
    have he := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    rw [hαsum] at he
    norm_num at he
  obtain ⟨i, hi⟩ := hex
  have he : α i * inhomogeneousTransition Q a t i i ≤ row Q α a t i := by
    exact Finset.single_le_sum (fun j _ => mul_nonneg (hα j)
      (integrableTransition_nonneg Q hQ hn ha hat j i)) (Finset.mem_univ i)
  have hp := (mul_pos hi (integrableTransition_diagonal_positive Q hQ hn ha hat i)).trans_le he
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => row_nonnegative Q α hQ hn hα ha hat j) (Finset.mem_univ i))

lemma density_nonnegative_ae (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hr : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) (hα : ∀ i, 0 ≤ α i)
    {a : ℝ} (ha : 0 ≤ a) : ∀ᵐ t, a ≤ t → 0 ≤ density Q α a t := by
  filter_upwards [hr] with t ht hat
  unfold density dotProduct
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (row_nonnegative Q α hQ hn hα ha hat i)
      (exitRate_nonneg (Q t) (ht (ha.trans hat)) i)

lemma law_mass_le_initial (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hr : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) (hα : ∀ i, 0 ≤ α i)
    {a : ℝ} (ha : 0 ≤ a) : law Q α a univ ≤ ENNReal.ofReal (∑ i, α i) := by
  have he := ac_flux_lintegral_le_initial (fun b _ => survival_ac Q α hQ a a b)
    (fun t ht => survival_nonnegative Q α hQ hn hα ha ht)
    (by filter_upwards [survival_derivative_ae Q α hQ a] with t ht _; exact ht)
    (density_nonnegative_ae Q α hQ hn hr hα ha)
    (density_locallyIntegrable Q α hQ a).aestronglyMeasurable.aemeasurable.restrict
  simpa only [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    survival_initial Q α hQ a] using he

lemma real_Ioc (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hn : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hr : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) (hα : ∀ i, 0 ≤ α i)
    {T : ℝ} (hT : 0 ≤ T) :
    (law Q α 0).real (Ioc 0 T) = (∑ i, α i) - survival Q α 0 T := by
  unfold law
  rw [positive_density_real_Ioc _ hT
    (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable
      (density_locallyIntegrable Q α hQ 0) 0 T), mass_balance Q α hQ]
  filter_upwards [(density_nonnegative_ae Q α hQ hn hr hα (le_refl (0 : ℝ))).filter_mono
    (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact ht hmem.1.le

end Rhone.Statistics.Identifiability.IntegrableWeightedExit
