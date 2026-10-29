/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MixedPoissonWeakConvergence
public import Rhone.Statistics.Identifiability.FiniteCountSeparationTopology

/-! # Weak observation of three-sample count vectors and the pan-invariant set -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ThreeSampleCounts

lemma continuous_branches : Continuous branches := by unfold branches; fun_prop
lemma continuous_durations : Continuous durations := by unfold durations; fun_prop

def countVector (rate : ℝ) (μ : ProbabilityMeasure (ℝ × ℝ)) (k : ℕ × ℕ) : ℝ :=
  (law rate μ).real {k}

lemma countVector_eq_mass (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) {rate : ℝ} (hrate : 0 ≤ rate)
    (k : ℕ × ℕ) : countVector rate μ k =
      MixedPoisson.mass rate rate ((μ : Measure (ℝ × ℝ)).map branches) k :=
  MixedPoisson.law_real_singleton _ (nonnegative_branch_law μ hμ) hrate hrate k

theorem tendsto_of_countVector_tendsto (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (target : ProbabilityMeasure (ℝ × ℝ))
    (hμ : ∀ n, FiniteSiteObservation.NonnegativeTimes (μ n))
    (htarget : FiniteSiteObservation.NonnegativeTimes target)
    {rate : ℝ} (hrate : 0 < rate)
    (hconv : ∀ k, Tendsto (fun n => countVector rate (μ n) k) atTop
      (𝓝 (countVector rate target k))) : Tendsto μ atTop (𝓝 target) := by
  let ν (n : ℕ) := (μ n).map branches
  let νtarget := target.map branches
  have hvn (n : ℕ) : FiniteSiteObservation.NonnegativeTimes (ν n) :=
    nonnegative_branch_law _ (hμ n)
  have hvtarget : FiniteSiteObservation.NonnegativeTimes νtarget :=
    nonnegative_branch_law _ htarget
  have hmass : ∀ k, Tendsto (fun n => MixedPoisson.mass rate rate (ν n) k) atTop
      (𝓝 (MixedPoisson.mass rate rate νtarget k)) := by
    intro k
    simpa only [countVector_eq_mass _ (hμ _) hrate.le,
      countVector_eq_mass target htarget hrate.le, ν, νtarget,
      ProbabilityMeasure.toMeasure_map] using hconv k
  have hν := MixedPoisson.tendsto_of_mass_tendsto ν νtarget hvn hvtarget hrate hrate hmass
  have hd := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    ν νtarget hν continuous_durations
  have hrecover (ρ : ProbabilityMeasure (ℝ × ℝ)) :
      (ρ.map branches).map durations = ρ := by
    apply ProbabilityMeasure.toMeasure_injective
    exact recover_duration_law ρ
  simpa only [ν, νtarget, hrecover] using hd

end ThreeSampleCounts
namespace FiniteCountSeparation

def firstCDF (μ : Measure (ℝ × ℝ)) (t : ℝ) : ℝ := (μ.map Prod.fst).real (Ioc 0 t)
def rootCDF (μ : Measure (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (μ.map (fun p => p.1 + p.2)).real (Ioc 0 t)

def PanInvariant (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    1 - firstCDF μ t = ((1 - firstCDF μ t) / 3 + 2 * (1 - rootCDF μ t) / 3) ^ 3

lemma tendsto_real_Ioc_of_tendsto {ι : Type*} {L : Filter ι}
    {μ : ι → ProbabilityMeasure ℝ} {target : ProbabilityMeasure ℝ}
    [NullSingletonClass (target : Measure ℝ)] (h : Tendsto μ L (𝓝 target)) (t : ℝ) :
    Tendsto (fun n => (μ n : Measure ℝ).real (Ioc 0 t)) L
      (𝓝 ((target : Measure ℝ).real (Ioc 0 t))) := by
  have hfrontier : (target : Measure ℝ) (frontier (Ioc (0 : ℝ) t)) = 0 := by
    by_cases ht : 0 < t
    · rw [frontier_Ioc ht]
      have hf : ({0, t} : Set ℝ).Finite := by simp
      exact hf.measure_zero _
    · rw [Ioc_eq_empty ht, frontier_empty, measure_empty]
  exact (ENNReal.tendsto_toReal (measure_ne_top (target : Measure ℝ) _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfrontier)

lemma panInvariant_of_tendsto (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (target : ProbabilityMeasure (ℝ × ℝ))
    [NullSingletonClass ((target : Measure (ℝ × ℝ)).map Prod.fst)]
    [NullSingletonClass ((target : Measure (ℝ × ℝ)).map (fun p => p.1 + p.2))]
    (hμ : ∀ n, PanInvariant (μ n)) (hlim : Tendsto μ atTop (𝓝 target)) :
    PanInvariant target := by
  let : NullSingletonClass
      ((target.map Prod.fst : ProbabilityMeasure ℝ) : Measure ℝ) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      (inferInstance : NullSingletonClass ((target : Measure (ℝ × ℝ)).map Prod.fst))
  let : NullSingletonClass
      ((target.map (fun p : ℝ × ℝ => p.1 + p.2) :
        ProbabilityMeasure ℝ) : Measure ℝ) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      (inferInstance : NullSingletonClass
        ((target : Measure (ℝ × ℝ)).map (fun p => p.1 + p.2)))
  intro t ht
  have hfirst : Tendsto (fun n => firstCDF (μ n) t) atTop (𝓝 (firstCDF target t)) := by
    exact tendsto_real_Ioc_of_tendsto
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ target hlim continuous_fst) t
  have hroot : Tendsto (fun n => rootCDF (μ n) t) atTop (𝓝 (rootCDF target t)) := by
    exact tendsto_real_Ioc_of_tendsto
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ target hlim
        (show Continuous (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop)) t
  have hleft := hfirst.const_sub 1
  have hright := ((hleft.div_const 3).add (((hroot.const_sub 1).const_mul 2).div_const 3)).pow 3
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (hμ n t ht).symm))

theorem uniform_count_box_of_pan_invariant {ι : Type*}
    (competitors : ι → ProbabilityMeasure (ℝ × ℝ))
    (target : ProbabilityMeasure (ℝ × ℝ))
    (hcompetitors : ∀ i, FiniteSiteObservation.NonnegativeTimes (competitors i))
    (htarget : FiniteSiteObservation.NonnegativeTimes target)
    [NullSingletonClass ((target : Measure (ℝ × ℝ)).map Prod.fst)]
    [NullSingletonClass ((target : Measure (ℝ × ℝ)).map (fun p => p.1 + p.2))]
    (hinvariant : ∀ i, PanInvariant (competitors i))
    (hviolation : ¬ PanInvariant target) {rate : ℝ} (hrate : 0 < rate) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ model : ι,
      ∃ i ≤ K, ∃ j ≤ K,
        ε ≤ |ThreeSampleCounts.countVector rate (competitors model) (i, j) -
          ThreeSampleCounts.countVector rate target (i, j)| := by
  classical
  let targetVector := ThreeSampleCounts.countVector rate target
  let C := range (fun i => ThreeSampleCounts.countVector rate (competitors i))
  have hsep : UniformBoxSeparation targetVector C := by
    apply uniform_box_of_no_pointwise_approximation
    intro p hp hconv
    choose model hmodel using hp
    have hconv' : ∀ k, Tendsto
        (fun n => ThreeSampleCounts.countVector rate (competitors (model n)) k) atTop
        (𝓝 (ThreeSampleCounts.countVector rate target k)) := by
      intro k
      simpa only [hmodel] using hconv k
    have hweak := ThreeSampleCounts.tendsto_of_countVector_tendsto
      (fun n => competitors (model n)) target (fun n => hcompetitors (model n))
      htarget hrate hconv'
    exact hviolation (panInvariant_of_tendsto _ target
      (fun n => hinvariant (model n)) hweak)
  obtain ⟨K, ε, hε, hsep⟩ := hsep
  exact ⟨K, ε, hε, fun model => hsep _ (mem_range_self model)⟩

end FiniteCountSeparation
end Rhone.Statistics.Identifiability
