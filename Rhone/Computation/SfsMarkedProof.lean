/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsProof
public import Rhone.Statistics.TajimaVariance

/-! # Executable pairwise formula moments under the marked Kingman law -/

@[expose] public section
namespace Rhone.Computation.Sfs
open MeasureTheory

theorem meanPairwise_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).meanPairwise : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi n x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanPi_mean hn rate
  rw [hrate] at h
  simpa [moments] using h.symm

theorem secondMomentPairwise_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).secondMomentPairwise : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi n x ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanPi_second_moment hn rate
  rw [hrate] at h
  simpa [moments, b1_eq, b2_eq] using h.symm

theorem variancePairwise_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).variancePairwise : Real) =
      ∫ x, (Rhone.Coalescent.markedKingmanPi n x - (theta : Real)) ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanPi_variance hn rate
  rw [hrate] at h
  simpa [moments, b1_eq, b2_eq] using h.symm

end Rhone.Computation.Sfs
