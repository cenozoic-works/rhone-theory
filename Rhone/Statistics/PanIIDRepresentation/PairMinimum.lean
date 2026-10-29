/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.PanPairTransform
public import Rhone.Statistics.Identifiability.PanThreeFactorization

/-! # The minimum of two pan pair times has doubled coalescence rate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.PanIIDRepresentation
open Algebra.Identifiability MarkovChain.Identifiability Identifiability

def pairMinimum (μ : Measure ℝ) : Measure ℝ := (μ.prod μ).map (fun p => min p.1 p.2)

lemma pairMinimum_real_tail (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (pairMinimum μ).real (Ioi t) = (μ.real (Ioi t))^2 := by
  rw [pairMinimum, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  have he : (fun p : ℝ × ℝ => min p.1 p.2) ⁻¹' Ioi t = Ioi t ×ˢ Ioi t := by
    ext p
    simp only [mem_preimage, mem_Ioi, lt_min_iff, mem_prod]
  rw [he, measureReal_prod_prod, pow_two]

lemma positive_real_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hp : ∀ᵐ x ∂μ, 0 < x) {t : ℝ} (ht : t ≤ 0) : μ.real (Ioi t) = 1 := by
  have he : Ioi t =ᵐ[μ] univ := hp.mono fun x hx =>
    propext ⟨fun _ => mem_univ x, fun _ => ht.trans_lt hx⟩
  rw [measureReal_congr he, probReal_univ]

theorem pairMinimum_pan (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop) :
    pairMinimum (panPairLaw r) = panPairLaw (fun t => 2 * r t) := by
  have h2 : LocallyIntegrable (fun t => 2 * r t) volume := by
    convert! hr.smul (2 : ℝ) using 1
  have hn2 : ∀ t, 0 ≤ 2 * r t := fun t => mul_nonneg (by norm_num) (hn t)
  have ht2 : Tendsto (integratedClock (fun t => 2 * r t)) atTop atTop := by
    change Tendsto (fun t => integratedClock (fun t => 2 * r t) t) atTop atTop
    simp_rw [integratedClock_scale]
    exact ht.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  let : IsProbabilityMeasure (panPairLaw (fun t => 2 * r t)) :=
    PanThreeSample.pairLaw_probability _ h2 hn2 ht2
  let : IsProbabilityMeasure (pairMinimum (panPairLaw r)) :=
    by change IsProbabilityMeasure (Measure.map _ _); infer_instance
  have tails : ∀ t, (pairMinimum (panPairLaw r)).real (Ioi t) =
      (panPairLaw (fun t => 2 * r t)).real (Ioi t) := by
    intro t
    rw [pairMinimum_real_tail]
    by_cases ht0 : 0 ≤ t
    · rw [PanThreeSample.pairLaw_real_Ioi r hr hn ht ht0,
        PanThreeSample.pairLaw_real_Ioi _ h2 hn2 ht2 ht0, integratedClock_scale,
        ← Real.exp_nat_mul]
      congr 1
      ring
    · rw [positive_real_tail _ (PanThreeSample.pairLaw_positive_support r) (le_of_not_ge ht0),
        positive_real_tail _ (PanThreeSample.pairLaw_positive_support _) (le_of_not_ge ht0)]
      norm_num
  apply Measure.ext_of_Iic
  intro t
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hleft := measureReal_add_measureReal_compl
    (μ := pairMinimum (panPairLaw r)) (s := Iic t) measurableSet_Iic
  have hright := measureReal_add_measureReal_compl
    (μ := panPairLaw (fun t => 2 * r t)) (s := Iic t) measurableSet_Iic
  simp only [compl_Iic, probReal_univ] at hleft hright
  change (pairMinimum (panPairLaw r)).real (Iic t) =
    (panPairLaw (fun t => 2 * r t)).real (Iic t)
  linarith [tails t]

end Rhone.Statistics.PanIIDRepresentation
