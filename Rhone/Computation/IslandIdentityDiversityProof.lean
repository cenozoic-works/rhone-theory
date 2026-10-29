/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.IslandIdentityLawProof

/-! # The explicit reference-diversity ratio equals existing identity differentiation -/

@[expose] public section
namespace Rhone.Computation.IslandIdentity

theorem within_cast (factor F : Rat) :
    (within factor F : Real) = (factor : Real) * (1 - (F : Real)) := by
  simp [within]

theorem between_cast (factor : Rat) : (between factor : Real) = (factor : Real) := rfl

theorem referenceRatio_cast (factor F : Rat) :
    (referenceRatio factor F : Real) =
      Rhone.Statistics.FStatistics.fRatio (factor * (1 - (F : Real))) factor := by
  simp [referenceRatio, within, between, Rhone.Statistics.FStatistics.fRatio]

theorem referenceRatio_eq_ibdFst (factor F : Rat) (hf : (factor : Real) ≠ 0) :
    (referenceRatio factor F : Real) = Rhone.Statistics.IslandIdentity.ibdFst F 0 := by
  rw [referenceRatio_cast, Rhone.Statistics.IslandIdentity.ibd_fst_diversity_bridge
    (F : Real) 0 (factor : Real) (by norm_num) hf]
  simp

theorem referenceRatio_eq_identity (factor F : Rat) (hf : (factor : Real) ≠ 0) :
    (referenceRatio factor F : Real) = (F : Real) := by
  rw [referenceRatio_eq_ibdFst factor F hf,
    Rhone.Statistics.IslandIdentity.ibd_fst_infinite_pool]

theorem generation_referenceRatio (N : Nat) (m F0 factor : Rat) (t : Nat)
    (hf : (factor : Real) ≠ 0) :
    (referenceRatio factor (generation N m t F0) : Real) =
      Rhone.Dynamics.ibdIter (2 * N) m t F0 := by
  rw [referenceRatio_eq_identity factor _ hf, generation_cast]

theorem equilibrium_referenceRatio (N : Nat) (m factor : Rat)
    (hf : (factor : Real) ≠ 0) :
    (referenceRatio factor (equilibrium N m) : Real) =
      Rhone.Dynamics.ibdFixed (2 * N) m := by
  rw [referenceRatio_eq_identity factor _ hf, equilibrium_cast]

end Rhone.Computation.IslandIdentity
