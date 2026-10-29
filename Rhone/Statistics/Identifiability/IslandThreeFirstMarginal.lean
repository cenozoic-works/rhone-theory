/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandThreeJointTimes
public import Rhone.Statistics.Identifiability.ThreeSampleCountObservation

/-! # Three-sample island joint density: row integrals, first marginal, and count law -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open MeasureTheory Set Filter
namespace Rhone.Statistics.Identifiability
namespace IslandThreeTimes

lemma shifted_pair_lintegral_one (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (j : Fin 2) (s : ℝ) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (postDensity k c q j (t-s))) = 1 := by
  let S : ℝ → ℝ := fun t => flowOutput (MarkovChain.Identifiability.pairGenerator k c q) j
      (fun _ => 1) 0 (t-s)
  have hd (t : ℝ) : HasDerivAt (fun u => 1-S u) (postDensity k c q j (t-s)) t := by
    have h := (survival_hasDerivAt_exit (MarkovChain.Identifiability.pairGenerator k c q) j
        (t-s)).comp t
      ((hasDerivAt_id t).sub_const s)
    simpa [S, postDensity] using h.const_sub 1
  have hn (t : ℝ) (ht : t ∈ Ioi s) : 0 ≤ postDensity k c q j (t-s) :=
    postDensity_nonneg k hc.le hq.le (sub_nonneg.mpr ht.le) j
  have htail : Tendsto S atTop (𝓝 0) := by
    apply (pair_survival_tendsto_zero k hc hq j).comp
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-s) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hi := integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hd t) hn (htail.const_sub 1)
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hd t) hn (htail.const_sub 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [he]
    simp [S]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hn t ht

lemma density_row_lintegral (k : ℕ) {c q s : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hs : 0 < s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (density k c q (s,t))) =
      ENNReal.ofReal (flowOutput (threeGenerator k c q) 0
        (exitRate (threeGenerator k c q)) 0 s) := by
  have h0 := entryFlux_nonneg k hc.le hq.le hs.le (0 : Fin 2)
  have h1 := entryFlux_nonneg k hc.le hq.le hs.le (1 : Fin 2)
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (density k c q (s,t))) =
      ∫⁻ t in Ioi s,
        ENNReal.ofReal (entryFlux k c q 0 s) *
          ENNReal.ofReal (postDensity k c q 0 (t-s)) +
        ENNReal.ofReal (entryFlux k c q 1 s) *
          ENNReal.ofReal (postDensity k c q 1 (t-s)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [density]
    rw [Fin.sum_univ_two, ENNReal.ofReal_add
      (mul_nonneg h0 (postDensity_nonneg k hc.le hq.le (sub_nonneg.mpr ht.le) 0))
      (mul_nonneg h1 (postDensity_nonneg k hc.le hq.le (sub_nonneg.mpr ht.le) 1)),
      ENNReal.ofReal_mul h0, ENNReal.ofReal_mul h1]
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (entryFlux k c q 0 s) *
      ENNReal.ofReal (postDensity k c q 0 (t-s))) :=
    measurable_const.mul (((postDensity_continuous k c q 0).comp
      (continuous_id.sub continuous_const)).measurable.ennreal_ofReal)
  rw [he, lintegral_add_left hm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    shifted_pair_lintegral_one k hc hq 0 s, shifted_pair_lintegral_one k hc hq 1 s,
    mul_one, mul_one, ← ENNReal.ofReal_add h0 h1]
  congr 1
  simpa only [Fin.sum_univ_two] using entryFlux_sum k c q s

theorem law_map_first (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    (law k c q).map Prod.fst = firstExitLaw (threeGenerator k c q) 0 := by
  rw [law, triangular_map_fst_ae _ (density_continuous k c q).measurable.aemeasurable]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact density_row_lintegral k hc hq hs

lemma law_ordered_ae (k : ℕ) (c q : ℝ) :
    ∀ᵐ p ∂law k c q, 0 < p.1 ∧ p.1 < p.2 := by
  change ∀ᵐ p ∂triangularDensityLaw (density k c q), p ∈ upperWedge
  rw [← triangular_restrict_upper (density k c q)]
  exact ae_restrict_mem upperWedge_open.measurableSet

def toDurations (p : ℝ × ℝ) : ℝ × ℝ := (p.1,p.2-p.1)
lemma measurable_toDurations : Measurable toDurations := by unfold toDurations; fun_prop

def durationLaw (k : ℕ) (c q : ℝ) : Measure (ℝ × ℝ) := (law k c q).map toDurations

theorem durationLaw_probability (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    IsProbabilityMeasure (durationLaw k c q) := by
  let : IsProbabilityMeasure (law k c q) := law_probability k hc hq
  unfold durationLaw
  exact inferInstance

theorem durationLaw_nonnegative (k : ℕ) (c q : ℝ) :
    FiniteSiteObservation.NonnegativeTimes (durationLaw k c q) := by
  unfold durationLaw FiniteSiteObservation.NonnegativeTimes
  apply (ae_map_iff measurable_toDurations.aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [law_ordered_ae k c q] with p hp
  exact ⟨hp.1.le, sub_nonneg.mpr hp.2.le⟩

theorem durationLaw_map_first (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    (durationLaw k c q).map Prod.fst = firstExitLaw (threeGenerator k c q) 0 := by
  rw [durationLaw, Measure.map_map measurable_fst measurable_toDurations]
  exact law_map_first k hc hq

theorem durationLaw_map_root (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    (durationLaw k c q).map (fun p => p.1+p.2) =
      firstExitLaw (islandThreeTreeGenerator k c q) 0 := by
  rw [durationLaw, Measure.map_map (by fun_prop) measurable_toDurations]
  have he : (fun p : ℝ × ℝ => p.1+p.2) ∘ toDurations = Prod.snd := by
    funext p
    dsimp [toDurations]
    ring
  rw [he]
  exact law_map_root k hc hq

def countLaw (k : ℕ) (c q rate : ℝ) : Measure (ℕ × ℕ) :=
  ThreeSampleCounts.law rate (durationLaw k c q)

theorem countLaw_probability (k : ℕ) {c q rate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ rate) : IsProbabilityMeasure (countLaw k c q rate) := by
  let : IsProbabilityMeasure (durationLaw k c q) := durationLaw_probability k hc hq
  exact ThreeSampleCounts.law_isProbability _ (durationLaw_nonnegative k c q) hr

end IslandThreeTimes
end Rhone.Statistics.Identifiability
