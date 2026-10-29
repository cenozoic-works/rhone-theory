/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExitLaw
public import Rhone.Statistics.Identifiability.EventMarks

/-! # The five first-merger marks partition a normalized exit measure -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open Filter Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def markFlux (k : Nat) (c q r : ℝ) (m : Fin 5) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.generator k c q r) 0 (fun i => markRates c i m) 0 t

theorem markFlux_continuous (k : Nat) (c q r : ℝ) (m : Fin 5) :
    Continuous (markFlux k c q r m) := flowOutput_continuous _ _ _ _

theorem markFlux_nonneg (k : Nat) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) (m : Fin 5) :
    0 ≤ markFlux k c q r m t := by
  simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg _ (generator_metzler k hc hq hr) ht)
    (fun i => markRates_nonneg hc i m) 0

theorem island_exitRate (k : Nat) (c q r : ℝ) (i : MarkovChain.Identifiability.State) :
    exitRate (MarkovChain.Identifiability.generator k c q r) i = c *
        (MarkovChain.Identifiability.killedCount (MarkovChain.Identifiability.shape i) : ℝ) := by
  simp only [exitRate, Pi.neg_apply, Matrix.mulVec, dotProduct, mul_one]
  rw [generator_row_sum]
  ring

theorem markFlux_partition (k : Nat) (c q r t : ℝ) :
    (∑ m, markFlux k c q r m t) =
      flowOutput (MarkovChain.Identifiability.generator k c q r) 0
          (exitRate (MarkovChain.Identifiability.generator k c q r)) 0 t := by
  simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, markRates_sum, island_exitRate]

noncomputable def markLaw (k : Nat) (c q r : ℝ) (m : Fin 5) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (markFlux k c q r m t))

theorem markLaws_sum (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    Measure.sum (markLaw k c q r) = firstExitLaw (MarkovChain.Identifiability.generator k c q r)
        0 := by
  unfold markLaw firstExitLaw
  rw [← withDensity_tsum (fun m => (markFlux_continuous k c q r m).measurable.ennreal_ofReal)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [tsum_fintype, Finset.sum_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => markFlux_nonneg k hc hq hr ht.le m),
    markFlux_partition]

theorem markLaw_total_mass (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    (∑' m, markLaw k c q r m univ) = 1 := by
  have := island_firstExitLaw_probability k hc hq hr
  rw [← Measure.sum_apply _ MeasurableSet.univ, markLaws_sum k hc.le hq.le hr, measure_univ]

end Rhone.Statistics.Identifiability
