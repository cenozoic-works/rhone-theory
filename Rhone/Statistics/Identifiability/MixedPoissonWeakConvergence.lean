/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MixedPoissonWeakKernels
public import Rhone.Statistics.Identifiability.FiniteCountTightness
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Inverse weak continuity of fixed-rate Poisson mixing -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Rhone.Statistics.Identifiability
namespace MixedPoisson

def partialKernel (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    (ℝ × ℝ) →ᵇ ℝ :=
  ∑ n ∈ Finset.range N, boundedCell a b (Nat.pairEquiv.symm n) ha hb

@[simp] lemma partialKernel_apply (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N : ℕ) (x : ℝ × ℝ) : partialKernel a b ha hb N x =
      ∑ n ∈ Finset.range N, boundedCell a b (Nat.pairEquiv.symm n) ha hb x := by
  exact BoundedContinuousFunction.sum_apply _ _ _

lemma partialKernel_le_one (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N : ℕ) (x : ℝ × ℝ) : partialKernel a b ha hb N x ≤ 1 := by
  have hs : HasSum (fun n : ℕ =>
      cell (a * |x.1|) (Nat.pairEquiv.symm n).1 *
        cell (b * |x.2|) (Nat.pairEquiv.symm n).2) 1 :=
    (Nat.pairEquiv.symm.hasSum_iff (f := fun k : ℕ × ℕ =>
      cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2)).mpr
        (hasSum_product (a * |x.1|) (b * |x.2|))
  rw [partialKernel_apply]
  exact sum_le_hasSum (Finset.range N)
    (fun n _ => boundedCell_nonneg a b (Nat.pairEquiv.symm n) ha hb x) hs

lemma partialKernel_vanishes {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    Tendsto (partialKernel a b ha.le hb.le N) (cocompact (ℝ × ℝ)) (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range N)
    (fun n _ => boundedCell_vanishes ha hb (Nat.pairEquiv.symm n))
  change Tendsto (fun x => partialKernel a b ha.le hb.le N x) _ _
  simp_rw [partialKernel_apply]
  simpa only [Finset.sum_const_zero] using h

lemma integral_partialKernel (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    (∫ x, partialKernel a b ha hb N x ∂μ) =
      ∑ n ∈ Finset.range N, mass a b μ (Nat.pairEquiv.symm n) := by
  simp_rw [partialKernel_apply]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun n _ => integral_boundedCell μ hμ a b _ ha hb
  · exact fun n _ => (boundedCell a b (Nat.pairEquiv.symm n) ha hb).integrable μ

lemma integral_partialKernel_tendsto (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun N => ∫ x, partialKernel a b ha hb N x ∂μ) atTop (𝓝 1) := by
  have hs : HasSum (mass a b μ) 1 := by
    simpa using mass_pgf_hasSum μ hμ ha hb
      (show (1 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have he : HasSum (fun n => mass a b μ (Nat.pairEquiv.symm n)) 1 :=
    (Nat.pairEquiv.symm.hasSum_iff (f := mass a b μ)).mpr hs
  simpa only [integral_partialKernel μ hμ a b ha hb] using he.tendsto_sum_nat

theorem isTight_of_mass_tendsto (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (target : ProbabilityMeasure (ℝ × ℝ))
    (hμ : ∀ n, FiniteSiteObservation.NonnegativeTimes (μ n))
    (htarget : FiniteSiteObservation.NonnegativeTimes target)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hconv : ∀ k, Tendsto (fun n => mass a b (μ n) k) atTop
      (𝓝 (mass a b target k))) :
    IsTightMeasureSet (range fun n => (μ n : Measure (ℝ × ℝ))) := by
  apply FiniteCountSeparation.isTight_of_vanishing_test_integrals μ target
    (partialKernel a b ha.le hb.le) (partialKernel_le_one a b ha.le hb.le)
    (partialKernel_vanishes ha hb)
    (integral_partialKernel_tendsto target htarget a b ha.le hb.le)
  intro m
  simp only [integral_partialKernel _ (hμ _) a b ha.le hb.le,
    integral_partialKernel target htarget a b ha.le hb.le]
  exact tendsto_finsetSum (Finset.range m) (fun n _ => hconv (Nat.pairEquiv.symm n))

lemma nonnegative_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {μ : ι → ProbabilityMeasure (ℝ × ℝ)} {target : ProbabilityMeasure (ℝ × ℝ)}
    (hμ : ∀ i, FiniteSiteObservation.NonnegativeTimes (μ i))
    (hlim : Tendsto μ L (𝓝 target)) :
    FiniteSiteObservation.NonnegativeTimes target := by
  let Q : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}
  have hQ : IsClosed Q :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  have hz (i : ι) : (μ i : Measure (ℝ × ℝ)) Qᶜ = 0 := by
    exact ae_iff.mp (hμ i)
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hQ.isOpen_compl
  simp only [hz, liminf_const] at h
  exact ae_iff.mpr (le_antisymm h bot_le)

theorem tendsto_of_mass_tendsto (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (target : ProbabilityMeasure (ℝ × ℝ))
    (hμ : ∀ n, FiniteSiteObservation.NonnegativeTimes (μ n))
    (htarget : FiniteSiteObservation.NonnegativeTimes target)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hconv : ∀ k, Tendsto (fun n => mass a b (μ n) k) atTop
      (𝓝 (mass a b target k))) :
    Tendsto μ atTop (𝓝 target) := by
  have htight := isTight_of_mass_tendsto μ target hμ htarget ha hb hconv
  refine (Filter.tendsto_iff_ultrafilter _ _ _).mpr fun U hU => ?_
  have hcompact : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      have heq : {((ν : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) |
          ν ∈ range μ} = range (fun n => (μ n : Measure (ℝ × ℝ))) := by
        ext ν
        simp
      rw [heq]
      exact htight)
  obtain ⟨ν, _, hν : Tendsto μ U (𝓝 ν)⟩ :=
    hcompact.ultrafilter_le_nhds (U.map μ)
      (.trans (by simp) (monotone_principal subset_closure))
  have hνnonneg := nonnegative_of_tendsto hμ hν
  have heq : (ν : Measure (ℝ × ℝ)) = target := by
    apply mass_injective ν target hνnonneg htarget ha hb
    intro k
    have hleft := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν
      (boundedCell a b k ha.le hb.le)
    simp only [integral_boundedCell _ (hμ _) a b k ha.le hb.le,
      integral_boundedCell ν hνnonneg a b k ha.le hb.le] at hleft
    exact tendsto_nhds_unique hleft ((hconv k).mono_left hU)
  have hνeq : ν = target := ProbabilityMeasure.toMeasure_injective heq
  simpa only [hνeq] using hν

end MixedPoisson
end Rhone.Statistics.Identifiability
