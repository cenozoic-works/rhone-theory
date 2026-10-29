/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairLaplaceTransform
public import Rhone.Statistics.Identifiability.FirstExitLaw
public import Rhone.Statistics.PairObservationChannel.LaplaceKernel

/-! # Symmetric-island pair-time bridge -/

@[expose] public section

open MeasureTheory Set
open scoped Matrix ENNReal
namespace Rhone.Statistics.SpatialPairDesign
open MarkovChain.Identifiability Identifiability PairObservationChannel

noncomputable def pairLaw (n : ℕ) (c q : ℝ) (i : Fin 2) : Measure ℝ :=
  firstExitLaw (pairGenerator n c q) i

theorem pair_rows_nonpos (n : ℕ) {c q : ℝ} (hc : 0 ≤ c) (i : Fin 2) :
    (∑ j, pairGenerator n c q i j) ≤ 0 := by
  fin_cases i <;> simp [pairGenerator, totalMigration, Fin.sum_univ_succ, hc]

theorem pair_law_probability (n : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (i : Fin 2) :
    IsProbabilityMeasure (pairLaw n c q i) :=
  firstExitLaw_probability _ (pairGenerator_metzler n hq.le) (pair_rows_nonpos n hc.le) i
    (pair_survival_tendsto_zero n hc hq i)

theorem pair_law_positive_support (n : ℕ) (c q : ℝ) (i : Fin 2) :
    ∀ᵐ t ∂pairLaw n c q i, 0 < t := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact ae_restrict_mem measurableSet_Ioi

theorem pairLaplace_pairLaw_eq_potential (n : ℕ) {c q k : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hk : 0 ≤ k) (i : Fin 2) :
    pairLaplace (pairLaw n c q i) k = pairLaplacePotential n c q k i := by
  have hQ := pairGenerator_metzler (c := c) n hq.le
  have hrow := pair_rows_nonpos (q := q) n hc.le
  have hreward := reward_integral_eq_potential (pairGenerator n c q - k • 1)
    (isMetzler_sub_scalar_identity hQ k) i (pairLaplacePotential n c q k) (pairDensity c)
    (pairLaplacePotential_equation n (pairLaplaceDenominator_pos n hc hq hk).ne')
    (by intro j; fin_cases j <;> simp [pairDensity, hc.le])
    (survival_sub_scalar_identity_tendsto_zero _ hQ hk i
      (pair_survival_tendsto_zero n hc hq i))
  simp only [flowOutput_sub_scalar_identity] at hreward
  unfold pairLaplace pairLaw firstExitLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (flowOutput_continuous (pairGenerator n c q) i
      (exitRate (pairGenerator n c q)) 0).measurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [← hreward]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hn := firstExit_density_nonneg _ hQ hrow i ht.le
  rw [pair_exitRate] at hn
  simp [pair_exitRate, ENNReal.toReal_ofReal hn, mul_comm]

theorem pairLaplace_gap (n : ℕ) {c q k : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hk : 0 ≤ k) :
    pairLaplace (pairLaw n c q 0) k - pairLaplace (pairLaw n c q 1) k =
      c * k / pairLaplaceDenominator n c q k := by
  rw [pairLaplace_pairLaw_eq_potential n hc hq hk, pairLaplace_pairLaw_eq_potential n hc hq hk]
  simp [pairLaplacePotential]
  ring

end Rhone.Statistics.SpatialPairDesign
