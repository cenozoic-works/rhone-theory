/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.IsGaloisGroup.Basic

/-! # Invariants descend to an integral root model -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

variable (A B K L G : Type*) [CommRing A] [IsIntegrallyClosed A]
    [CommRing B] [Field K] [Field L] [Group G]
    [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FaithfulSMul B L] [Algebra.IsIntegral A B]
    [MulSemiringAction G B] [MulSemiringAction G L] [SMulDistribClass G B L]
    [Algebra.IsInvariant K L G]

include K L in
theorem invariant_of_integral_model : Algebra.IsInvariant A B G := by
  constructor
  intro b hb
  have hbL : IsIntegral A (algebraMap B L b) :=
    (Algebra.IsIntegral.isIntegral b).algebraMap
  obtain ⟨k, hk⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := G) (algebraMap B L b)
    (fun g => by rw [← algebraMap.coe_smul', hb g])
  have hkint : IsIntegral A k := by
    rw [← hk, isIntegral_algebraMap_iff] at hbL
    exact hbL
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hkint
  refine ⟨a, FaithfulSMul.algebraMap_injective B L ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply] using hk

end Rhone.Algebra.GaloisSpecialization
