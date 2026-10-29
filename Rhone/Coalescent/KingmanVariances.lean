/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanPathMoments
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Tactic.Ring
/-!
# Variances of the Kingman jump-and-hold path functionals

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset MarkovChain
open scoped ENNReal
private theorem measurable_block_cost (n : ℕ) (g : ℕ → ℝ) :
    Measurable ((blockChain n).costBefore (coalesced n) (fun k => g k)) := by
  unfold RateChain.costBefore RateChain.holdTime
  apply Measurable.tsum
  intro k
  have hstate : Measurable (fun p : (ℕ → Fin (n + 1)) × (ℕ → ℝ) => p.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have hset := (MeasurableSet.of_discrete
    (s := {k : Fin (n + 1) | k ∈ coalesced n})).preimage hstate
  have hg : Measurable (fun k : Fin (n + 1) => g k) := Measurable.of_discrete
  have hr : Measurable (blockChain n).rate := Measurable.of_discrete
  exact measurable_const.ite hset
    (((hg.comp hstate).mul
      (((measurable_pi_apply k).comp measurable_snd).div (hr.comp hstate))).ennreal_ofReal)
private theorem variance_of_ennreal_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞)
    (hX : Measurable X) (m v : ℝ) (hm : 0 ≤ m) (hv : 0 ≤ v)
    (hfirst : ∫⁻ p, X p ∂μ = ENNReal.ofReal m)
    (hsecond : ∫⁻ p, (X p) ^ 2 ∂μ = ENNReal.ofReal (m ^ 2 + v)) :
    variance (fun p => (X p).toReal) μ = v := by
  have hfinite : ∀ᵐ p ∂μ, X p < ∞ := ae_lt_top hX (by
    rw [hfirst]
    exact ENNReal.ofReal_ne_top)
  have hfinite2 : ∀ᵐ p ∂μ, (X p) ^ 2 < ∞ := by
    filter_upwards [hfinite] with p hp
    exact ENNReal.pow_lt_top hp
  have hpow : (fun p => ((X p) ^ 2).toReal) = fun p => (X p).toReal ^ 2 := by
    funext p
    exact ENNReal.toReal_pow _ _
  have hint2 := integrable_toReal_of_lintegral_ne_top (hX.pow_const 2).aemeasurable (by
    rw [hsecond]
    exact ENNReal.ofReal_ne_top)
  rw [hpow] at hint2
  have hlp : MemLp (fun p => (X p).toReal) 2 μ :=
    (memLp_two_iff_integrable_sq hX.ennreal_toReal.aestronglyMeasurable).2 hint2
  rw [variance_eq_sub hlp]
  have hmean : ∫ p, (X p).toReal ∂μ = m := by
    rw [integral_toReal hX.aemeasurable hfinite, hfirst, ENNReal.toReal_ofReal hm]
  have hsq : ∫ p, ((X p).toReal) ^ 2 ∂μ = m ^ 2 + v := by
    rw [← hpow, integral_toReal (hX.pow_const 2).aemeasurable hfinite2,
      hsecond, ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) hv)]
  change (∫ p, ((X p).toReal) ^ 2 ∂μ) - (∫ p, (X p).toReal ∂μ) ^ 2 = v
  rw [hsq, hmean]
  ring
theorem variance_tmrca (n : ℕ) :
    ProbabilityTheory.variance (fun p => (tmrca n p).toReal)
      ((blockChain n).jumpHoldLaw (Fin.last n)) = (varTMRCA n : ℝ) := by
  apply variance_of_ennreal_moments _ _
    (measurable_block_cost n (fun _ => 1)) (expTMRCA n : ℝ)
  · have hm : (0 : ℚ) ≤ expTMRCA n := by
      unfold expTMRCA holdingTime
      exact sum_nonneg fun k _ => div_nonneg (by norm_num) (coalRate_nonneg k)
    exact_mod_cast hm
  · have hv : (0 : ℚ) ≤ varTMRCA n := by
      unfold varTMRCA
      exact sum_nonneg fun k _ => sq_nonneg (holdingTime k)
    exact_mod_cast hv
  · exact lintegral_tmrca n
  · exact lintegral_tmrca_sq n
theorem variance_treeLength (n : ℕ) :
    ProbabilityTheory.variance (fun p => (treeLength n p).toReal)
      ((blockChain n).jumpHoldLaw (Fin.last n)) = (varLength n : ℝ) := by
  apply variance_of_ennreal_moments _ _
    (measurable_block_cost n (fun k => (k : ℝ))) (expLength n : ℝ)
  · have hm : (0 : ℚ) ≤ expLength n := by
      unfold expLength holdingTime
      exact sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k)
        (div_nonneg (by norm_num) (coalRate_nonneg k))
    exact_mod_cast hm
  · have hv : (0 : ℚ) ≤ varLength n := by
      unfold varLength
      exact sum_nonneg fun k _ => sq_nonneg ((k : ℚ) * holdingTime k)
    exact_mod_cast hv
  · exact lintegral_treeLength n
  · exact lintegral_treeLength_sq n
end Rhone.Coalescent
