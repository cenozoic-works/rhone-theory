/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableFlux
public import Rhone.Statistics.Identifiability.PairIntegrableFlow

/-! # Literal sampling projection and first-merger properness for locally L1 source histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma projectedRow_initial (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    projectedRow k c q 0 = Pi.single 0 1 := by
  unfold projectedRow
  rw [preRow_initial k c q hc hq]
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, pairProjection, Pi.single_apply]

lemma projectedRow_ac (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (a b : ℝ) (j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun u => projectedRow k c q u j) a b :=
  finiteRowMatrixProduct_entry_ac (preRow k c q) (fun _ => pairProjection) a b
    (preRow_ac k c q hc hq a b)
    (fun i l =>
      (LipschitzWith.const (pairProjection i l)).lipschitzOnWith.absolutelyContinuousOnInterval) j

lemma projectedRow_derivative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, ∀ j, HasDerivAt (fun u => projectedRow k c q u j)
      ((projectedRow k c q t ᵥ* MarkovChain.Identifiability.pairGenerator k (c t) (q t) - lostFlux k
          c q t) j) t := by
  filter_upwards [preRow_derivative_ae k c q hc hq] with t ht j
  have h := finiteRowMatrixProduct_hasDerivAt_at (preRow k c q) (fun _ => pairProjection)
    (preRow k c q t ᵥ* threeGenerator k (c t) (q t)) 0 t ht
    (fun i l => hasDerivAt_const t (pairProjection i l)) j
  simp only [Matrix.vecMul_zero, add_zero] at h
  have hb := congrArg (fun M => preRow k c q t ᵥ* M) (projection_generator k (c t) (q t))
  simp only [Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul] at hb
  apply h.congr_deriv
  exact congrFun (eq_sub_of_add_eq hb) j

lemma lostFlux_nonnegative_at (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {t : ℝ} (ht : 0 ≤ t) (hct : 0 ≤ c t) (j : Fin 2) :
    0 ≤ lostFlux k c q t j :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (firstFlux_nonnegative_at k c q hc hq hqn ht hct j)

lemma projection_duhamel (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) :
    projectedRow k c q t +
      (fun j => ∫ u in (0 : ℝ)..t,
        (lostFlux k c q u ᵥ* timeVaryingPairTransition k c q u t) j) =
      timeVaryingPairTransition k c q 0 t 0 := by
  have h := finiteRow_projection_duhamel_integrable
      (fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u))
    (PairIntegrable.generator_locallyIntegrable k c q hc hq)
    (projectedRow k c q) (lostFlux k c q) 0 t (projectedRow_ac k c q hc hq 0 t) (by
      filter_upwards [projectedRow_derivative_ae k c q hc hq] with u hu _ j
      exact hu j)
  rw [projectedRow_initial k c q hc hq] at h
  simpa only [Matrix.single_vecMul, one_smul, Matrix.row, timeVaryingPairTransition] using h

lemma survival_le_pair (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {t : ℝ} (ht : 0 ≤ t) : survival k c q t ≤ timeVaryingPairSurvival k c q 0 0 t := by
  rw [← projectedRow_sum]
  apply Finset.sum_le_sum
  intro j _
  have hi : 0 ≤ ∫ u in (0 : ℝ)..t,
      (lostFlux k c q u ᵥ* timeVaryingPairTransition k c q u t) j := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht
    filter_upwards [hcn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Icc] with u hu hmem
    change 0 ≤ ∑ i, lostFlux k c q u i * timeVaryingPairTransition k c q u t i j
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (lostFlux_nonnegative_at k c q hc hq hqn hmem.1 (hu hmem.1) i)
        (PairIntegrable.transition_nonnegative k c q hc hq hqn hmem.1 hmem.2 i j)
  have he := congrFun (projection_duhamel k c q hc hq t) j
  simp only [Pi.add_apply] at he
  linarith

lemma survival_tendsto_zero_of_pair (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (survival k c q) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hproper
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (survival_positive k c q hc hq hqn ht).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_le_pair k c q hc hq hcn hqn ht

end Rhone.Statistics.Identifiability.ThreeIntegrable
