/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MixedPoissonInjection

/-! # Exact probability laws for three-sample unfolded infinite-sites counts -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.Identifiability
namespace MixedPoisson

lemma mass_nonneg (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ × ℕ) :
    0 ≤ mass a b μ k := by
  apply integral_nonneg_of_ae
  filter_upwards [hμ] with x hx
  exact mul_nonneg (cell_nonneg (mul_nonneg ha hx.1) _)
    (cell_nonneg (mul_nonneg hb hx.2) _)

def law (a b : ℝ) (μ : Measure (ℝ × ℝ)) : Measure (ℕ × ℕ) :=
  Measure.sum fun k => ENNReal.ofReal (mass a b μ k) • Measure.dirac k

lemma law_real_singleton (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ × ℕ) :
    (law a b μ).real {k} = mass a b μ k := by
  rw [measureReal_def, law, Measure.sum_smul_dirac_singleton,
    ENNReal.toReal_ofReal (mass_nonneg μ hμ ha hb k)]

lemma law_isProbability (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsProbabilityMeasure (law a b μ) := by
  have hs : HasSum (fun k : ℕ × ℕ => mass a b μ k) 1 := by
    simpa using mass_pgf_hasSum μ hμ ha hb
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  exact HasSum.isProbabilityMeasure_sum_dirac (mass_nonneg μ hμ ha hb) hs

theorem law_injective (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (heq : law a b μ = law a b ν) : μ = ν := by
  apply mass_injective μ ν hμ hν ha hb
  intro k
  rw [← law_real_singleton μ hμ ha.le hb.le k,
    ← law_real_singleton ν hν ha.le hb.le k, heq]

end MixedPoisson

namespace ThreeSampleCounts

def branches (t : ℝ × ℝ) : ℝ × ℝ := (3 * t.1 + t.2, t.2)

def durations (x : ℝ × ℝ) : ℝ × ℝ := ((x.1 - x.2) / 3, x.2)

lemma measurable_branches : Measurable branches := by unfold branches; fun_prop
lemma measurable_durations : Measurable durations := by unfold durations; fun_prop

lemma durations_branches (t : ℝ × ℝ) : durations (branches t) = t := by
  apply Prod.ext
  · dsimp [durations, branches]
    ring
  · rfl

lemma recover_duration_law (μ : Measure (ℝ × ℝ)) :
    (μ.map branches).map durations = μ := by
  rw [Measure.map_map measurable_durations measurable_branches]
  have heq : durations ∘ branches = id := funext durations_branches
  rw [heq, Measure.map_id]

lemma nonnegative_branch_law (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) :
    FiniteSiteObservation.NonnegativeTimes (μ.map branches) := by
  unfold FiniteSiteObservation.NonnegativeTimes
  apply (ae_map_iff measurable_branches.aemeasurable
    (show MeasurableSet {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [hμ] with t ht
  dsimp [branches]
  exact ⟨by linarith [ht.1, ht.2], ht.2⟩

def law (rate : ℝ) (μ : Measure (ℝ × ℝ)) : Measure (ℕ × ℕ) :=
  MixedPoisson.law rate rate (μ.map branches)

lemma law_isProbability (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) {rate : ℝ} (hrate : 0 ≤ rate) :
    IsProbabilityMeasure (law rate μ) := by
  let : IsProbabilityMeasure (μ.map branches) :=
    inferInstance
  exact MixedPoisson.law_isProbability _ (nonnegative_branch_law μ hμ) hrate hrate

theorem law_injective (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    {rate : ℝ} (hrate : 0 < rate) (heq : law rate μ = law rate ν) : μ = ν := by
  have hmap : μ.map branches = ν.map branches :=
    MixedPoisson.law_injective _ _ (nonnegative_branch_law μ hμ)
      (nonnegative_branch_law ν hν) hrate hrate heq
  have h := congrArg (Measure.map durations) hmap
  simpa only [recover_duration_law] using h

end ThreeSampleCounts
end Rhone.Statistics.Identifiability
