/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockPanReconstruction
public import Rhone.Statistics.Identifiability.IndependentClockObservation
public import Rhone.Statistics.Identifiability.NonnegativeLaplaceUniqueness

/-! # Common-clock observations identify the marginal sum, the joint law, and both rates -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem nonnegative_univariate_laplace_unique
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (he : ∀ n : ℕ, (∫ t, Real.exp (-(n : ℝ) * t) ∂μ) =
      ∫ t, Real.exp (-(n : ℝ) * t) ∂ν) : μ = ν := by
  let e := fun t : ℝ => (t, (0 : ℝ))
  have hm : Measurable e := measurable_id.prodMk measurable_const
  have hn (ξ : Measure ℝ) (hξ : ∀ᵐ t ∂ξ, 0 ≤ t) :
      FiniteSiteObservation.NonnegativeTimes (ξ.map e) := by
    apply (ae_map_iff hm.aemeasurable (show MeasurableSet
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
        (measurableSet_le measurable_const measurable_fst).inter
          (measurableSet_le measurable_const measurable_snd))).mpr
    filter_upwards [hξ] with t ht
    exact ⟨ht, le_rfl⟩
  have hmap : μ.map e = ν.map e := by
    apply nonnegative_bivariate_laplace_unique _ _ (hn μ hμ) (hn ν hν)
    intro m n
    rw [integral_map hm.aemeasurable (by fun_prop), integral_map hm.aemeasurable (by fun_prop)]
    simpa only [e, mul_zero, Real.exp_zero, mul_one] using he m
  have heq := congrArg (fun ξ : Measure (ℝ × ℝ) => ξ.map Prod.fst) hmap
  rw [Measure.map_map measurable_fst hm, Measure.map_map measurable_fst hm] at heq
  have hid : Prod.fst ∘ e = id := by funext x; rfl
  rwa [hid, Measure.map_id, Measure.map_id] at heq

theorem common_clock_observations_identify_marginal_sum
    {K : ℕ} {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    (he : ∀ k : ℝ, 0 < k → FiniteSiteObservation.law K k μ = FiniteSiteObservation.law K k ν) :
    μ.map Prod.fst = ν.map Prod.fst ∧
      μ.map (fun p => p.1 + p.2) = ν.map (fun p => p.1 + p.2) := by
  have hsm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have htrans (k : ℝ) (hk : 0 < k) := IndependentClockObservation.laplace_eq_of_law_eq
    hK hk.le hk.le hμ hν (by
      simpa only [IndependentClockObservation.law_commonClock hK] using he k hk)
  have hfst (ξ : Measure (ℝ × ℝ)) (hξ : FiniteSiteObservation.NonnegativeTimes ξ) :
      ∀ᵐ t ∂ξ.map Prod.fst, 0 ≤ t := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ici).mpr
    exact hξ.mono (fun _ ht => ht.1)
  have hsum (ξ : Measure (ℝ × ℝ)) (hξ : FiniteSiteObservation.NonnegativeTimes ξ) :
      ∀ᵐ t ∂ξ.map (fun p => p.1 + p.2), 0 ≤ t := by
    apply (ae_map_iff hsm.aemeasurable measurableSet_Ici).mpr
    exact hξ.mono (fun _ ht => add_nonneg ht.1 ht.2)
  constructor
  · apply nonnegative_univariate_laplace_unique _ _ (hfst μ hμ) (hfst ν hν)
    intro n
    rw [integral_map measurable_fst.aemeasurable (by fun_prop),
      integral_map measurable_fst.aemeasurable (by fun_prop)]
    by_cases hn : n = 0
    · simp [hn]
    · have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      simpa only [IndependentClockObservation.laplace, mul_zero, zero_mul,
        neg_zero, Real.exp_zero, mul_one, neg_mul] using (htrans n hp).1
  · apply nonnegative_univariate_laplace_unique _ _ (hsum μ hμ) (hsum ν hν)
    intro n
    rw [integral_map hsm.aemeasurable (by fun_prop),
      integral_map hsm.aemeasurable (by fun_prop)]
    by_cases hn : n = 0
    · simp [hn]
    · have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h := (htrans n hp).2.2
      simp only [IndependentClockObservation.laplace, ← Real.exp_add] at h
      convert h using 1 <;> congr 1 <;> funext t <;> congr 1 <;> ring

theorem ProperIntegrablePanModel.common_clock_observations_identify_jointLaw
    (P Q : ProperIntegrablePanModel) {K : ℕ} (hK : 2 ≤ K) (h : ℝ → ℝ)
    (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hr : ∀ᵐ t, 0 ≤ t → P.rate t = h t)
    (he : ∀ k : ℝ, 0 < k → FiniteSiteObservation.law K k P.pre.jointLaw =
      FiniteSiteObservation.law K k Q.pre.jointLaw) : P.pre.jointLaw = Q.pre.jointLaw := by
  let := P.jointLaw_probability
  let := Q.jointLaw_probability
  have hd := common_clock_observations_identify_marginal_sum hK
    (FiniteSiteObservation.pan_nonnegativeTimes P) (FiniteSiteObservation.pan_nonnegativeTimes Q) he
  exact P.marginal_sum_identifies_jointLaw Q h hh hn hr hd.1 hd.2

theorem ProperIntegrablePanModel.common_clock_observations_identify_both_rates
    (P Q : ProperIntegrablePanModel) {K : ℕ} (hK : 2 ≤ K) (h : ℝ → ℝ)
    (hh : Continuous h) (hpos : ∀ t, 0 < t → 0 < h t)
    (hr : ∀ᵐ t, 0 ≤ t → P.rate t = h t)
    (he : ∀ k : ℝ, 0 < k → FiniteSiteObservation.law K k P.pre.jointLaw =
      FiniteSiteObservation.law K k Q.pre.jointLaw) :
    (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) ∧
      (∀ᵐ t, 0 ≤ t → P.pre.recomb t = Q.pre.recomb t) := by
  let := P.jointLaw_probability
  let := Q.jointLaw_probability
  have hd := common_clock_observations_identify_marginal_sum hK
    (FiniteSiteObservation.pan_nonnegativeTimes P) (FiniteSiteObservation.pan_nonnegativeTimes Q) he
  exact P.marginal_sum_identifies_both_rates Q h hh hpos hr hd.1 hd.2

theorem ProperIntegrablePanModel.common_clock_observations_identify_of_pair_density
    (P Q : ProperIntegrablePanModel) {K : ℕ} (hK : 2 ≤ K) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ici 0)) (hpos : ∀ t ≥ 0, 0 < f t)
    (hpair : P.pre.jointLaw.map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (f t)))
    (he : ∀ k : ℝ, 0 < k → FiniteSiteObservation.law K k P.pre.jointLaw =
      FiniteSiteObservation.law K k Q.pre.jointLaw) :
    P.pre.jointLaw = Q.pre.jointLaw ∧
      (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) ∧
      (∀ᵐ t, 0 ≤ t → P.pre.recomb t = Q.pre.recomb t) := by
  let := P.jointLaw_probability
  let := Q.jointLaw_probability
  have hd := common_clock_observations_identify_marginal_sum hK
    (FiniteSiteObservation.pan_nonnegativeTimes P) (FiniteSiteObservation.pan_nonnegativeTimes Q) he
  exact P.pair_density_sum_identifies Q f hf hpos hpair hd.1 hd.2

end Rhone.Statistics.Identifiability
