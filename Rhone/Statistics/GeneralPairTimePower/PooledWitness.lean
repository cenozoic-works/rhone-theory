/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.GeneralPairTimePower.Observation
public import Rhone.Statistics.Identifiability.PanPairTailProbability
public import Rhone.Statistics.ErlangPhase.DurationProduct
public import Rhone.Statistics.PooledPairPowerIndex.Pooled

/-! # Proper constant-pan witness, for the full reported pair law -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
namespace Rhone.Statistics.GeneralPairTimePower
open DependenceBudget PairObservationChannel MarkovChain.Identifiability Identifiability
open PooledPairPowerIndex
variable {K : ℕ} {H : Type*} [Fintype H]

def AdmittedPan (r : ℝ → ℝ) : Prop :=
  LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧ Tendsto (integratedClock r) atTop atTop

theorem constant_pan_admitted {a : ℝ} (ha : 0 < a) : AdmittedPan (fun _ => a) := by
  refine ⟨continuous_const.locallyIntegrable, fun _ => ha.le, ?_⟩
  have he : integratedClock (fun _ => a) = fun t => a * t := by
    funext t
    simp [integratedClock, mul_comm]
  rw [he]
  exact tendsto_id.const_mul_atTop ha

theorem constant_pan_exponential (a : ℝ) :
    panPairLaw (fun _ => a) = FoldedCounts.exponential a := by
  simp [panPairLaw, FoldedCounts.exponential, mul_comm]

def matchingRate (k L : ℝ) : ℝ := k * L / (1 - L)

theorem matching_rate_pos {k L : ℝ} (hk : 0 < k) (hL : 0 < L ∧ L < 1) :
    0 < matchingRate k L := div_pos (mul_pos hk hL.1) (sub_pos.mpr hL.2)

theorem matching_rate_laplace {k L : ℝ} (hk : 0 < k) (hL : 0 < L ∧ L < 1) :
    pairLaplace (panPairLaw (fun _ => matchingRate k L)) k = L := by
  rw [constant_pan_exponential]
  rw [show pairLaplace _ k = _ from
    ErlangPhase.exponential_laplace _ k (matching_rate_pos hk hL) hk.le]
  unfold matchingRate
  have hn : 1 - L ≠ 0 := ne_of_gt (sub_pos.mpr hL.2)
  have hd : k * L / (1 - L) + k ≠ 0 := ne_of_gt
    (add_pos (div_pos (mul_pos hk hL.1) (sub_pos.mpr hL.2)) hk)
  field_simp [hn, hd]
  ring

def panObservedLaw (E : Channel K H) (r : ℝ → ℝ) (hr : AdmittedPan r)
    {k : ℝ} (hk : 0 ≤ k) : Law (H × H) := by
  letI := PanThreeSample.pairLaw_probability r hr.1 hr.2.1 hr.2.2
  exact observedLaw E (panPairLaw r) hk ((PanThreeSample.pairLaw_positive_support r).mono
    (fun _ h => h.le))

theorem matching_observed_law (E : Channel K H) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℝ} (hk : 0 < k) (hμ : ∀ᵐ t ∂μ, 0 < t) :
    panObservedLaw E (fun _ => matchingRate k (pairLaplace μ k))
      (constant_pan_admitted (matching_rate_pos hk (laplace_strict_interval μ hk hμ))) hk.le =
        observedLaw E μ hk.le (hμ.mono fun _ h => h.le) := by
  apply LinkedPairMoments.finite_law_ext
  intro x
  change reportedMass E (pairLaplace (panPairLaw (fun _ => matchingRate k (pairLaplace μ k))) k)
    x.1 x.2 = reportedMass E (pairLaplace μ k) x.1 x.2
  rw [matching_rate_laplace hk (laplace_strict_interval μ hk hμ)]

def pooledLaplace (μ ν : Measure ℝ) (k : ℝ) : ℝ := (pairLaplace μ k + pairLaplace ν k) / 2

theorem pooled_laplace_interval (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t) :
    0 < pooledLaplace μ ν k ∧ pooledLaplace μ ν k < 1 := by
  have h1 := laplace_strict_interval μ hk hμ
  have h2 := laplace_strict_interval ν hk hν
  unfold pooledLaplace
  constructor <;> linarith

theorem pooled_reported_law (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t) :
    panObservedLaw E (fun _ => matchingRate k (pooledLaplace μ ν k))
      (constant_pan_admitted (matching_rate_pos hk (pooled_laplace_interval μ ν hk hμ hν))) hk.le =
        pooledLaw (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
          (observedLaw E ν hk.le (hν.mono fun _ h => h.le)) := by
  apply LinkedPairMoments.finite_law_ext
  intro x
  change reportedMass E (pairLaplace (panPairLaw
    (fun _ => matchingRate k (pooledLaplace μ ν k))) k) x.1 x.2 =
      (reportedMass E (pairLaplace μ k) x.1 x.2 +
        reportedMass E (pairLaplace ν k) x.1 x.2) / 2
  rw [matching_rate_laplace hk (pooled_laplace_interval μ ν hk hμ hν)]
  unfold reportedMass pooledLaplace
  ring

end Rhone.Statistics.GeneralPairTimePower
