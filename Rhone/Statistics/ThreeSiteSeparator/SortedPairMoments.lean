/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedPairMarginals
public import Rhone.Statistics.ThreeSiteSeparator.SortedPairWeighted
public import Rhone.Statistics.ThreeSiteSeparator.CDFMoments

/-! # Exact mixed moments of the sorted-iid law, using only CDF continuity -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

theorem sortedPair_mixed_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hF : Continuous (fun x => μ.real (Iic x))) (p q : ℕ) :
    (∫ z, z.1^(p+1)*z.2^(q+1) ∂sortedPairLaw μ) =
      cdfMixedMoment (p+1) (q+1) (fun x => μ.real (Iic x)) := by
  let : IsProbabilityMeasure (sortedPairLaw μ) := sortedPairLaw_probability μ
  rw [joint_moment_CDF _ (sortedPairLaw_unit_support μ hμ),
    sortedPair_fst_moment μ hμ, sortedPair_snd_moment μ hμ hF,
    sortedPair_weighted_CDF μ hF, cdfJointWeighted_reduction hF]
  unfold cdfMixedMoment cdfCrossIntegral weightedPrimitive
  have hn : p+1+(q+1)-1 = p+q+1 := by omega
  simp only [Nat.add_sub_cancel, hn, Nat.cast_add, Nat.cast_one]
  ring

theorem sortedPair_pair_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hF : Continuous (fun x => μ.real (Iic x))) (r : ℕ) :
    ((∫ z, z.1^(r+1) ∂sortedPairLaw μ)+2*(∫ z, z.2^(r+1) ∂sortedPairLaw μ))/3 =
      cdfPairMoment (r+1) (fun x => μ.real (Iic x)) := by
  rw [sortedPair_fst_moment μ hμ, sortedPair_snd_moment μ hμ hF]
  unfold cdfPairMoment
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

end Rhone.Statistics.ThreeSiteSeparator
