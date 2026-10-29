/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableDiagonalLowerBound
public import Rhone.Statistics.Identifiability.TimeVaryingPairExitKernel

/-! # Pair evolution under locally L1 island histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.PairIntegrable

lemma generator_affine (k : ℕ) (c q : ℝ) :
    MarkovChain.Identifiability.pairGenerator k c q = c • MarkovChain.Identifiability.pairGenerator
        k 1 0 + q • MarkovChain.Identifiability.pairGenerator k 0 1 := by
  ext i j
  change MarkovChain.Identifiability.pairGenerator k c q i j = c *
      MarkovChain.Identifiability.pairGenerator k 1 0 i j + q *
      MarkovChain.Identifiability.pairGenerator k 0 1 i j
  fin_cases i <;> fin_cases j <;> simp
      [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.totalMigration] <;>
      ring

lemma generator_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ i j, LocallyIntegrable (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j)
        volume := by
  intro i j
  have he : (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) =
      fun t => c t * MarkovChain.Identifiability.pairGenerator k 1 0 i j + q t *
          MarkovChain.Identifiability.pairGenerator k 0 1 i j := by
    funext t
    rw [generator_affine]
    rfl
  rw [he]
  exact (hc.mul_continuous continuous_const).add (hq.mul_continuous continuous_const)

lemma generator_metzler_ae (k : ℕ) (c q : ℝ → ℝ) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) :
    ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ MarkovChain.Identifiability.pairGenerator k (c u) (q u) i j :=
        by
  filter_upwards [hqn] with u hu hnonneg
  exact pairGenerator_metzler k (hu hnonneg)

lemma transition_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i j : Fin 2) :
    0 ≤ timeVaryingPairTransition k c q s t i j :=
  integrableTransition_nonneg _ (generator_locallyIntegrable k c q hc hq)
    (generator_metzler_ae k c q hqn) hs hst i j

lemma transition_diagonal_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : Fin 2) :
    0 < timeVaryingPairTransition k c q s t i i :=
  integrableTransition_diagonal_positive _ (generator_locallyIntegrable k c q hc hq)
    (generator_metzler_ae k c q hqn) hs hst i

lemma transition_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (fun p : ℝ × ℝ => timeVaryingPairTransition k c q p.1 p.2) :=
  integrableTransition_continuous _ (generator_locallyIntegrable k c q hc hq)

lemma survival_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : Fin 2) :
    0 ≤ timeVaryingPairSurvival k c q s i t :=
  Finset.sum_nonneg fun j _ => transition_nonnegative k c q hc hq hqn hs hst i j

lemma survival_restart (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (s u t : ℝ) (i : Fin 2) :
    timeVaryingPairSurvival k c q s i t =
      ∑ j, timeVaryingPairTransition k c q s u i j * timeVaryingPairSurvival k c q u j t := by
  unfold timeVaryingPairSurvival timeVaryingPairTransition
  rw [integrableTransition_cocycle _ (generator_locallyIntegrable k c q hc hq) s u t]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma survival_ac (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (s a b : ℝ) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (timeVaryingPairSurvival k c q s i) a b :=
  ac_finset_sum Finset.univ fun j _ =>
    integrableTransition_entry_ac_right _ (generator_locallyIntegrable k c q hc hq) s a b i j

lemma survival_derivative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, ∀ s i, HasDerivAt (timeVaryingPairSurvival k c q s i)
      (-timeVaryingPairExitDensity k c q s i t) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right _
    (generator_locallyIntegrable k c q hc hq)] with t ht s i
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht s i j)).congr_deriv
  change (∑ j, ∑ l, timeVaryingPairTransition k c q s t i l *
      MarkovChain.Identifiability.pairGenerator k (c t) (q t) l j) = _
  simp [timeVaryingPairExitDensity, MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_two]
  ring

end Rhone.Statistics.Identifiability.PairIntegrable
