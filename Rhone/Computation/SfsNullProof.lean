/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsNull
public import Rhone.Computation.SfsProof
public import Rhone.Statistics.WattersonMarkedMoments

/-! # Law identification of the four executable total-S and Watterson moments -/

@[expose] public section
namespace Rhone.Computation.SfsNull
open MeasureTheory

theorem meanSegregating_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).meanSegregating : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating n x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanSegregating_mean hn rate
  rw [hrate] at h
  simpa [moments, Sfs.moments, Sfs.a1_eq] using h.symm

theorem varianceSegregating_eq_variance (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).varianceSegregating : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanSegregating n)
        (Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta))) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanSegregating_variance hn rate
  rw [hrate] at h
  simpa [moments, Sfs.moments, Sfs.a1_eq, Sfs.a2_eq] using h.symm

theorem meanWatterson_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).meanWatterson : Real) =
      ∫ x, Rhone.Statistics.markedKingmanWatterson n x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanWatterson_mean hn rate
  rw [hrate] at h
  simpa [moments] using h.symm

theorem varianceWatterson_eq_variance (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    ((moments n theta).varianceWatterson : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanWatterson n)
        (Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta))) := by
  let rate : NNReal := NNReal.mk (theta : Real) (by exact_mod_cast htheta)
  have hrate : (rate : Real) = (theta : Real) := NNReal.coe_mk _ _
  have h := Rhone.Statistics.markedKingmanWatterson_variance hn rate
  rw [hrate] at h
  simpa [moments, Sfs.a1_eq, Sfs.a2_eq] using h.symm

end Rhone.Computation.SfsNull
