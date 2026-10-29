/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.Pan
public import Rhone.Statistics.WeakRegularSeparation.CompactMarginal
public import Rhone.Statistics.WeakRegularSeparation.ExactComparison

/-! # Maximum-coordinate marginal and exclusion of noncandidate laws from the compact family -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites

theorem max_encoded {k : ℝ} (hk : 0 ≤ k) (g : Joint)
    (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2) : maxEncoding (encode k g) = Real.exp (-k * g.1.1) := by
  have he : Real.exp (-k * (g.1.1 + g.1.2)) ≤ Real.exp (-k * g.1.1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold maxEncoding
  simp_rw [encode_value hk g hg, pair_means_coordinate]
  generalize cherryCoordinate g.2 = q
  fin_cases q <;> simp <;> nlinarith

theorem encoded_max_marginal {k : ℝ} (hk : 0 ≤ k) (μ : Measure Joint)
    [IsProbabilityMeasure μ] (hμ : NonnegativeJoint μ) :
    (encodedProbability k μ : Measure (Cube 3)).map maxEncoding =
      (μ.map (fun g : Joint => g.1.1)).map (fun u => Real.exp (-k * u)) := by
  change Measure.map maxEncoding (μ.map (encode k)) = _
  rw [Measure.map_map max_encoding_continuous.measurable (encode_measurable k),
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hμ] with g hg
  exact max_encoded hk g hg

theorem encoded_eq_positive_candidate {k : ℝ} (hk : 0 < k)
    (μ ν : Measure Joint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν)
    (hvν : ∀ᵐ g ∂ν, 0 < g.1.2)
    (he : encodedProbability k μ = encodedProbability k ν) : μ = ν := by
  apply (collapsed_eq_iff_joint_eq μ ν hvν).mp
  apply (object_eq_iff_collapsed_eq hk.ne' μ ν).mp
  rw [← decoded_encoding_map hk.le μ hμ, ← decoded_encoding_map hk.le ν hν]
  exact congrArg (fun ρ : ProbabilityMeasure (Cube 3) =>
    (ρ : Measure (Cube 3)).map (fun x => decode (fun i => (x i).val))) he

theorem outside_compact_of_distinct_candidate {k : ℝ} (hk : 0 < k)
    (μ ν : Measure Joint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν)
    (hvν : ∀ᵐ g ∂ν, 0 < g.1.2)
    (hfirst : μ.map (fun g : Joint => g.1.1) = ν.map (fun g : Joint => g.1.1))
    (hpan : encodedProbability k ν ∈ range compactPan) (hne : μ ≠ ν) :
    encodedProbability k μ ∉ range compactPan := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hpan
  have hm : (compactPan a : Measure (Cube 3)).map maxEncoding =
      (compactPan b : Measure (Cube 3)).map maxEncoding := by
    rw [ha, hb, encoded_max_marginal hk.le μ hμ, encoded_max_marginal hk.le ν hν, hfirst]
  have hab := compact_pan_max_injective hm
  apply hne
  apply encoded_eq_positive_candidate hk μ ν hμ hν hvν
  rw [← ha, ← hb, hab]

end Rhone.Statistics.WeakRegularSeparation
