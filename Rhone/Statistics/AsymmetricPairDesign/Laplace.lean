/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AsymmetricPairDesign.Potential
public import Rhone.Statistics.AsymmetricPairDesign.Balance
public import Rhone.Statistics.Identifiability.PairLaplaceTransform

/-! # Laplace transforms of the asymmetric first-exit laws equal the rational potentials -/

@[expose] public section

open scoped Matrix Topology ENNReal
open MeasureTheory Set Filter
namespace Rhone.Statistics.AsymmetricPairDesign
open MarkovChain.Identifiability Identifiability

noncomputable def laplace (a b c d k : ℝ) (i : Fin 3) : ℝ :=
  ∫ t, Real.exp (-k * t) ∂pairLaw a b c d i

theorem laplace_eq_potential {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) (i : Fin 3) :
    laplace a b c d k i = potential a b c d k i := by
  have hQ := generator_metzler (c := c) (d := d) ha.le hb.le
  have hrow : ∀ j, (∑ l, generator a b c d j l) ≤ 0 := by
    intro j
    rw [generator_row_sum]
    fin_cases j <;> simp [rate, hc.le, hd.le]
  have hreward := reward_integral_eq_potential (generator a b c d - k • 1)
    (isMetzler_sub_scalar_identity hQ k) i (potential a b c d k) (rate c d)
    (potential_equation (denominator_pos ha hb hc hd hk).ne')
    (by intro j; fin_cases j <;> simp [rate, hc.le, hd.le])
    (survival_sub_scalar_identity_tendsto_zero _ hQ hk i
      (survival_vanishes ha hb hc hd i))
  simp only [flowOutput_sub_scalar_identity] at hreward
  unfold laplace pairLaw firstExitLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (flowOutput_continuous (generator a b c d) i
      (exitRate (generator a b c d)) 0).measurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [← hreward]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hn := firstExit_density_nonneg _ hQ hrow i ht.le
  rw [exit_rate] at hn
  simp [exit_rate, ENNReal.toReal_ofReal hn, mul_comm]

theorem laplace_balance {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) :
    (k + a + b) * laplace a b c d k 1 =
      b * laplace a b c d k 0 + a * laplace a b c d k 2 := by
  simp_rw [laplace_eq_potential ha hb hc hd hk]
  exact potential_balance (denominator_pos ha hb hc hd hk).ne'

theorem laplace_separation {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    laplace a b c d k 1 < laplace a b c d k 0 ∨
      laplace a b c d k 1 < laplace a b c d k 2 := by
  apply balance_separation ha hb hk _ (laplace_balance ha hb hc hd hk.le)
  rw [laplace_eq_potential ha hb hc hd hk.le]
  exact potential_pos ha hb hc hd hk.le 1

end Rhone.Statistics.AsymmetricPairDesign
