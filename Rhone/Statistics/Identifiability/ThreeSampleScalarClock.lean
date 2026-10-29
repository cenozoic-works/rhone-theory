/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleFiniteCountSeparation

/-! # One finite count experiment with an unknown positive scalar mutation clock -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ScalarCountClock
set_option backward.isDefEq.respectTransparency false

def scaleTimes (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (a * p.1, a * p.2)

lemma measurable_scaleTimes (a : ℝ) : Measurable (scaleTimes a) := by
  unfold scaleTimes
  fun_prop

def scaleProbability (a : ℝ) (μ : ProbabilityMeasure (ℝ × ℝ)) :
    ProbabilityMeasure (ℝ × ℝ) := μ.map (scaleTimes a)

lemma nonnegative_scaleProbability {a : ℝ} (ha : 0 ≤ a)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : FiniteSiteObservation.NonnegativeTimes μ) :
    FiniteSiteObservation.NonnegativeTimes (scaleProbability a μ) := by
  change FiniteSiteObservation.NonnegativeTimes ((μ : Measure (ℝ × ℝ)).map (scaleTimes a))
  unfold FiniteSiteObservation.NonnegativeTimes
  apply (ae_map_iff (measurable_scaleTimes a).aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [hμ] with p hp
  exact ⟨mul_nonneg ha hp.1, mul_nonneg ha hp.2⟩

lemma countVector_eq_integral (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ × ℕ) : ThreeSampleCounts.countVector r μ k =
      ∫ p, MixedPoisson.cell (r * (3 * p.1 + p.2)) k.1 *
        MixedPoisson.cell (r * p.2) k.2 ∂(μ : Measure (ℝ × ℝ)) := by
  rw [ThreeSampleCounts.countVector_eq_mass μ hμ hr]
  unfold MixedPoisson.mass
  have hm : Continuous (fun p : ℝ × ℝ =>
      MixedPoisson.cell (r * p.1) k.1 * MixedPoisson.cell (r * p.2) k.2) := by
    unfold MixedPoisson.cell
    fun_prop
  rw [integral_map ThreeSampleCounts.measurable_branches.aemeasurable
    hm.aestronglyMeasurable]
  rfl

lemma countVector_scaleProbability (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) {a r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (k : ℕ × ℕ) :
    ThreeSampleCounts.countVector r (scaleProbability a μ) k =
      ThreeSampleCounts.countVector (r * a) μ k := by
  rw [countVector_eq_integral _ (nonnegative_scaleProbability ha μ hμ) hr,
    countVector_eq_integral μ hμ (mul_nonneg hr ha)]
  change (∫ p, MixedPoisson.cell (r * (3 * p.1 + p.2)) k.1 *
    MixedPoisson.cell (r * p.2) k.2 ∂((μ : Measure (ℝ × ℝ)).map (scaleTimes a))) = _
  have hm : Continuous (fun p : ℝ × ℝ =>
      MixedPoisson.cell (r * (3 * p.1 + p.2)) k.1 *
        MixedPoisson.cell (r * p.2) k.2) := by
    unfold MixedPoisson.cell
    fun_prop
  rw [integral_map (measurable_scaleTimes a).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    dsimp [scaleTimes]
    congr 2 <;> ring

lemma scaled_projection_Ioc (μ : Measure (ℝ × ℝ)) {a : ℝ} (ha : 0 < a)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hscale : ∀ p, f (scaleTimes a p) = a * f p) (t : ℝ) :
    ((μ.map (scaleTimes a)).map f).real (Ioc 0 t) =
      (μ.map f).real (Ioc 0 (t / a)) := by
  unfold Measure.real
  rw [Measure.map_map hf (measurable_scaleTimes a),
    Measure.map_apply (hf.comp (measurable_scaleTimes a)) measurableSet_Ioc,
    Measure.map_apply hf measurableSet_Ioc]
  congr 1
  congr 1
  ext p
  change (0 < f (scaleTimes a p) ∧ f (scaleTimes a p) ≤ t) ↔
    (0 < f p ∧ f p ≤ t / a)
  rw [hscale]
  constructor
  · intro hp
    exact ⟨(mul_pos_iff_of_pos_left ha).mp hp.1, (le_div_iff₀ ha).mpr (by linarith [hp.2])⟩
  · intro hp
    exact ⟨mul_pos ha hp.1, by nlinarith [(le_div_iff₀ ha).mp hp.2]⟩

lemma firstCDF_scaleProbability (μ : ProbabilityMeasure (ℝ × ℝ)) {a : ℝ}
    (ha : 0 < a) (t : ℝ) :
    FiniteCountSeparation.firstCDF (scaleProbability a μ) t =
      FiniteCountSeparation.firstCDF μ (t / a) := by
  exact scaled_projection_Ioc μ ha Prod.fst measurable_fst (fun _ => rfl) t

lemma rootCDF_scaleProbability (μ : ProbabilityMeasure (ℝ × ℝ)) {a : ℝ}
    (ha : 0 < a) (t : ℝ) :
    FiniteCountSeparation.rootCDF (scaleProbability a μ) t =
      FiniteCountSeparation.rootCDF μ (t / a) := by
  apply scaled_projection_Ioc μ ha (fun p => p.1 + p.2) (by fun_prop) _ t
  intro p
  dsimp [scaleTimes]
  ring

lemma pan_invariant_at (rate : FiniteCountSeparation.ProperHazard) {t : ℝ} (ht : 0 ≤ t) :
    1 - FiniteCountSeparation.firstCDF (FiniteCountSeparation.panDuration rate) t =
      ((1 - FiniteCountSeparation.firstCDF (FiniteCountSeparation.panDuration rate) t) / 3 +
        2 * (1 - FiniteCountSeparation.rootCDF
          (FiniteCountSeparation.panDuration rate) t) / 3) ^ 3 := by
  have hfirst : 1 - FiniteCountSeparation.firstCDF (FiniteCountSeparation.panDuration rate) t =
      Real.exp (-3 * integratedClock rate.val t) := by
    change 1 - ((PanThreeSample.durationLaw rate.val).map Prod.fst).real (Ioc 0 t) = _
    rw [PanThreeSample.durationLaw_first_marginal rate.val rate.property.1
      rate.property.2.1 rate.property.2.2,
      ← PanThreeSample.first_marginal rate.val rate.property.1
        rate.property.2.1 rate.property.2.2]
    exact PanThreeSample.first_survival rate.val rate.property.1
      rate.property.2.1 rate.property.2.2 ht
  have hroot : 1 - FiniteCountSeparation.rootCDF (FiniteCountSeparation.panDuration rate) t =
      (3/2 : ℝ) * Real.exp (-integratedClock rate.val t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate.val t) := by
    change 1 - ((PanThreeSample.durationLaw rate.val).map
      (fun p => p.1 + p.2)).real (Ioc 0 t) = _
    rw [PanThreeSample.durationLaw_root_cdf rate.val rate.property.1 rate.property.2.1 ht]
    ring
  rw [hfirst, hroot]
  have heq : Real.exp (-3 * integratedClock rate.val t) / 3 +
      2 * ((3/2 : ℝ) * Real.exp (-integratedClock rate.val t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate.val t)) / 3 =
      Real.exp (-integratedClock rate.val t) := by ring
  rw [heq, ← Real.exp_nat_mul]
  congr 1
  ring

lemma scaled_pan_invariant (rate : FiniteCountSeparation.ProperHazard) {a : ℝ}
    (ha : 0 < a) :
    FiniteCountSeparation.PanInvariant
      (scaleProbability a (FiniteCountSeparation.panDuration rate)) := by
  intro t ht
  rw [firstCDF_scaleProbability _ ha, rootCDF_scaleProbability _ ha]
  exact pan_invariant_at rate (div_nonneg ht.1 ha.le)

end ScalarCountClock
end Rhone.Statistics.Identifiability
