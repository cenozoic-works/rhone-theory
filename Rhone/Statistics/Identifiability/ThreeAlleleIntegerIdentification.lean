/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeAlleleObservationLaw
public import Rhone.Statistics.Identifiability.CommonClockObservations

/-! # Integer-mutation-rate observations identify the pair-time sum law -/

@[expose] public section

open Set MeasureTheory
noncomputable section

namespace Rhone.Statistics.Identifiability.ThreeAlleleMutation

theorem nonnegative_laplace_unique_positive_grid
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha : 0 < a) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (he : ∀ n : ℕ, 0 < n →
      (∫ t, Real.exp (-(a * (n : ℝ)) * t) ∂μ) =
        ∫ t, Real.exp (-(a * (n : ℝ)) * t) ∂ν) : μ = ν := by
  have hscale : Measurable (fun t : ℝ => a * t) := measurable_const.mul measurable_id
  have hnonneg (ξ : Measure ℝ) (hξ : ∀ᵐ t ∂ξ, 0 ≤ t) :
      ∀ᵐ t ∂ξ.map (fun t => a * t), 0 ≤ t := by
    apply (ae_map_iff hscale.aemeasurable measurableSet_Ici).mpr
    exact hξ.mono (fun _ ht => mul_nonneg ha.le ht)
  have hscaled : μ.map (fun t => a * t) = ν.map (fun t => a * t) := by
    apply nonnegative_univariate_laplace_unique _ _ (hnonneg μ hμ) (hnonneg ν hν)
    intro n
    rw [integral_map hscale.aemeasurable (by fun_prop),
      integral_map hscale.aemeasurable (by fun_prop)]
    by_cases hn : n = 0
    · simp [hn]
    · convert he n (Nat.pos_of_ne_zero hn) using 1 <;>
        congr 1 <;> funext t <;> congr 1 <;> ring
  have hundo : Measurable (fun t : ℝ => t / a) := measurable_id.div_const a
  have heq := congrArg (Measure.map (fun t : ℝ => t / a)) hscaled
  rw [Measure.map_map hundo hscale, Measure.map_map hundo hscale] at heq
  have hid : (fun t : ℝ => t / a) ∘ (fun t => a * t) = id := by
    funext t
    simp [mul_div_cancel_left₀, ha.ne']
  rwa [hid, Measure.map_id, Measure.map_id] at heq

theorem integer_observations_identify_pair_sum
    {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    (he : ∀ n : ℕ, 0 < n → law (n : ℝ) μ = law (n : ℝ) ν) :
    μ.map Prod.fst = ν.map Prod.fst ∧
      μ.map (fun p => p.1 + p.2) = ν.map (fun p => p.1 + p.2) := by
  have hsm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  let : IsProbabilityMeasure (μ.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure (ν.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure (μ.map (fun p => p.1 + p.2)) :=
    inferInstance
  let : IsProbabilityMeasure (ν.map (fun p => p.1 + p.2)) :=
    inferInstance
  have htrans (n : ℕ) (hn : 0 < n) :=
    laplace_eq_of_law_eq (show 0 ≤ (n : ℝ) by positivity) hμ hν (he n hn)
  have hfst (ξ : Measure (ℝ × ℝ)) (hξ : FiniteSiteObservation.NonnegativeTimes ξ) :
      ∀ᵐ t ∂ξ.map Prod.fst, 0 ≤ t := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ici).mpr
    exact hξ.mono (fun _ ht => ht.1)
  have hsum (ξ : Measure (ℝ × ℝ)) (hξ : FiniteSiteObservation.NonnegativeTimes ξ) :
      ∀ᵐ t ∂ξ.map (fun p => p.1 + p.2), 0 ≤ t := by
    apply (ae_map_iff hsm.aemeasurable measurableSet_Ici).mpr
    exact hξ.mono (fun _ ht => add_nonneg ht.1 ht.2)
  constructor
  · apply nonnegative_laplace_unique_positive_grid _ _ (show (0 : ℝ) < 5 by norm_num)
      (hfst μ hμ) (hfst ν hν)
    intro n hn
    rw [integral_map measurable_fst.aemeasurable (by fun_prop),
      integral_map measurable_fst.aemeasurable (by fun_prop)]
    simpa only [IndependentClockObservation.laplace, mul_zero, zero_mul,
      neg_zero, Real.exp_zero, mul_one, neg_mul] using (htrans n hn).1
  · apply nonnegative_laplace_unique_positive_grid _ _ (show (0 : ℝ) < 5 by norm_num)
      (hsum μ hμ) (hsum ν hν)
    intro n hn
    rw [integral_map hsm.aemeasurable (by fun_prop),
      integral_map hsm.aemeasurable (by fun_prop)]
    have h := (htrans n hn).2.2.1
    simp only [IndependentClockObservation.laplace, ← Real.exp_add] at h
    convert h using 1 <;> congr 1 <;> funext t <;> congr 1 <;> ring

end Rhone.Statistics.Identifiability.ThreeAlleleMutation
