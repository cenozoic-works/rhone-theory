/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ExitCDF

/-! # First-exit mass balance for arbitrary finite initial sampling mixtures -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability.WeightedExit
variable {n : ℕ}

def survival (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, α i * flowOutput Q i (fun _ => 1) 0 t

def density (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, α i * flowOutput Q i (exitRate Q) 0 t

def law (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (density Q α t))

lemma density_continuous (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) :
    Continuous (density Q α) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (flowOutput_continuous Q i _ 0))

lemma density_nonnegative (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (hα : ∀ i, 0 ≤ α i)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ density Q α t := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (firstExit_density_nonneg Q hQ hrow i ht)

lemma survival_derivative (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (survival Q α) (-density Q α t) t := by
  have hd := HasDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
    (survival_hasDerivAt_exit Q i t).const_mul (α i)
  convert! hd using 1
  · ext s; simp [survival]
  · simp [density, Finset.sum_neg_distrib]

lemma mass_balance (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) :
    (∫ s in 0..t, density Q α s) = (∑ i, α i) - survival Q α t := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => survival_derivative Q α s)
    ((density_continuous Q α).neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at he
  have hz : survival Q α 0 = ∑ i, α i := by simp [survival]
  rw [hz] at he
  linarith

lemma real_Ioc (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (hα : ∀ i, 0 ≤ α i)
    {t : ℝ} (ht : 0 ≤ t) :
    (law Q α).real (Ioc 0 t) = (∑ i, α i) - survival Q α t := by
  unfold law
  rw [positive_density_real_Ioc _ ht ((density_continuous Q α).intervalIntegrable 0 t),
    mass_balance]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact density_nonnegative Q α hQ hrow hα hs.1.le

end Rhone.Statistics.Identifiability.WeightedExit
