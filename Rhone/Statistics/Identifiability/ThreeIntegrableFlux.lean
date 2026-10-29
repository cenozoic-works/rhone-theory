/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableOnset
public import Rhone.Statistics.Identifiability.IntegrableDiagonalLowerBound
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingJointLaw

/-! # Pre-merger masses and fluxes under locally L1 source histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma preRow_derivative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, ∀ i, HasDerivAt (fun u => preRow k c q u i)
      ((preRow k c q t ᵥ* threeGenerator k (c t) (q t)) i) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right _
    (preGenerator_locallyIntegrable k c q hc hq)] with t ht i
  exact ht 0 0 i

lemma preRow_ac (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (a b : ℝ) (i : ThreeState) :
    AbsolutelyContinuousOnInterval (fun t => preRow k c q t i) a b :=
  integrableTransition_entry_ac_right _ (preGenerator_locallyIntegrable k c q hc hq) 0 a b 0 i

lemma preRow_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (i : ThreeState) :
    Continuous (fun t => preRow k c q t i) := by
  have hU := integrableTransition_continuous _ (preGenerator_locallyIntegrable k c q hc hq)
  change Continuous (fun t => inhomogeneousTransition _ 0 t 0 i)
  fun_prop

lemma preRow_initial (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    preRow k c q 0 = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [preRow,
    integrableTransition_self _ (preGenerator_locallyIntegrable k c q hc hq)]

lemma preGenerator_metzler_ae (k : ℕ) (c q : ℝ → ℝ) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ threeGenerator k (c t) (q t) i j := by
  filter_upwards [hqn] with t ht hnonneg
  exact threeGenerator_metzler k (c t) (ht hnonneg)

lemma preRow_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) (i : ThreeState) :
    0 ≤ preRow k c q t i :=
  integrableTransition_nonneg _ (preGenerator_locallyIntegrable k c q hc hq)
    (preGenerator_metzler_ae k c q hqn) le_rfl ht 0 i

lemma preRow_initial_coordinate_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) : 0 < preRow k c q t 0 :=
  integrableTransition_diagonal_positive _ (preGenerator_locallyIntegrable k c q hc hq)
    (preGenerator_metzler_ae k c q hqn) le_rfl ht 0

lemma survival_initial (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    survival k c q 0 = 1 := by
  simp only [survival, preRow_initial k c q hc hq]
  simp

lemma survival_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) : 0 < survival k c q t :=
  (preRow_initial_coordinate_positive k c q hc hq hqn ht).trans_le
    (Finset.single_le_sum (fun i _ => preRow_nonnegative k c q hc hq hqn ht i) (Finset.mem_univ 0))

lemma survival_ac (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (survival k c q) a b :=
  ac_finset_sum Finset.univ fun i _ => preRow_ac k c q hc hq a b i

lemma survival_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (survival k c q) :=
  continuous_finsetSum _ fun i _ => preRow_continuous k c q hc hq i

lemma survival_derivative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, HasDerivAt (survival k c q) (-firstDensity k c q t) t := by
  filter_upwards [preRow_derivative_ae k c q hc hq] with t ht
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)).congr_deriv
  simp [firstDensity, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    threeGenerator, MarkovChain.Identifiability.totalMigration, mergerWeight]
  ring

lemma firstDensity_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    LocallyIntegrable (firstDensity k c q) volume :=
  hc.mul_continuous (continuous_finsetSum _ fun i _ =>
    (preRow_continuous k c q hc hq i).mul continuous_const)

lemma firstFlux_nonnegative_at (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {t : ℝ} (ht : 0 ≤ t) (hct : 0 ≤ c t) (j : Fin 2) :
    0 ≤ firstFlux k c q t j := by
  change 0 ≤ ∑ i, preRow k c q t i * IslandThreeTimes.firstRate (c t) i j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (preRow_nonnegative k c q hc hq hqn ht i)
    (IslandThreeTimes.firstRate_nonneg hct i j)

lemma firstDensity_nonnegative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ firstDensity k c q t := by
  filter_upwards [hcn] with t ht hnonneg
  rw [← firstFlux_sum]
  exact Finset.sum_nonneg fun j _ => firstFlux_nonnegative_at k c q hc hq hqn hnonneg (ht hnonneg) j

end Rhone.Statistics.Identifiability.ThreeIntegrable
