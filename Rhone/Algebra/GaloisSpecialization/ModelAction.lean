/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.RootModel
public import Rhone.Algebra.GaloisSpecialization.IntegralModel

/-! # The faithful group action on the integral root model, and its invariants -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {A L G : Type*} [CommRing A] [Field L] [Algebra A L]
    [Group G] [MulSemiringAction G L] [SMulCommClass G A L]

instance rootModel_mulSemiringAction (p : A[X]) : MulSemiringAction G (rootModel A L p) :=
  inferInstanceAs (MulSemiringAction G (rootModel A L p).toSubring)

instance rootModel_smulCommClass (p : A[X]) : SMulCommClass G A (rootModel A L p) where
  smul_comm g a b := Subtype.ext (smul_comm g a (b : L))

instance rootModel_smulDistribClass (p : A[X]) : SMulDistribClass G (rootModel A L p) L where
  smul_distrib_smul g b x := by
    change g • ((b : L) * x) = (g • (b : L)) * (g • x)
    exact smul_mul' g (b : L) x

variable {K : Type*} [Field K] [Algebra K L]

theorem rootModel_faithful [SMulCommClass G K L] [FaithfulSMul G L] (p : A[X])
    (hgen : Algebra.adjoin K (p.rootSet L) = ⊤) : FaithfulSMul G (rootModel A L p) := by
  constructor
  intro g h hgh
  have he : MulSemiringAction.toAlgHom K L g = MulSemiringAction.toAlgHom K L h := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    exact congrArg Subtype.val (hgh (⟨x, Algebra.subset_adjoin hx⟩ : rootModel A L p))
  exact eq_of_smul_eq_smul (α := L) fun x => DFunLike.congr_fun he x

variable [IsIntegrallyClosed A] [Algebra A K] [IsFractionRing A K]
    [IsScalarTower A K L] [Algebra.IsInvariant K L G]

include K in
theorem rootModel_invariant (p : A[X]) (hp : p.Monic) :
    Algebra.IsInvariant A (rootModel A L p) G := by
  have := rootModel_integral (L := L) hp
  exact invariant_of_integral_model A (rootModel A L p) K L G

end Rhone.Algebra.GaloisSpecialization
