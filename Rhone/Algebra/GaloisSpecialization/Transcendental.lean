/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.GenericGroup
public import Rhone.Algebra.GaloisDegreeSeven.AlgClosed

/-! # Full symmetric Galois groups persist over a rational-function extension -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {k : Type*} [Field k]

theorem galois_full_ratFunc_of_galois_full (p : k[X]) (hsep : p.Separable)
    (hsep' : (p.map (algebraMap k (RatFunc k))).Separable)
    (hfull : Function.Bijective (Gal.galActionHom p p.SplittingField)) :
    Function.Bijective (Gal.galActionHom (p.map (algebraMap k (RatFunc k)))
      (p.map (algebraMap k (RatFunc k))).SplittingField) := by
  classical
  let q := p.map (C : k →+* k[X])
  have hspec : q.map (evalRingHom (0 : k)) = p := by
    rw [map_map]
    have h : (evalRingHom (0 : k)).comp (C : k →+* k[X]) = RingHom.id k := by
      ext x
      simp
    rw [h, map_id]
  have hgen : q.map (algebraMap k[X] (RatFunc k)) = p.map (algebraMap k (RatFunc k)) := by
    rw [map_map, Rhone.Algebra.GaloisDegreeSeven.algebraMap_comp_C]
  have hlc : (evalRingHom (0 : k)) q.leadingCoeff ≠ 0 := by
    change (evalRingHom (0 : k)) (p.map C).leadingCoeff ≠ 0
    rw [leadingCoeff_map_of_injective C_injective]
    simpa using leadingCoeff_ne_zero.mpr hsep.ne_zero
  have hsep₀ : (q.map (evalRingHom (0 : k))).Separable := hspec.symm ▸ hsep
  have hsepq : (q.map (algebraMap k[X] (RatFunc k))).Separable := hgen.symm ▸ hsep'
  have hcard : Fintype.card (q.map (evalRingHom (0 : k))).Gal =
      q.natDegree.factorial := by
    rw [hspec, Fintype.card_of_bijective hfull, Fintype.card_perm,
      card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)]
    exact congrArg Nat.factorial (natDegree_map_eq_of_injective C_injective p).symm
  have h := generic_galois_full_of_specialization q 0 hlc hsep₀ hsepq hcard
  exact Eq.mp (congrArg (fun r : (RatFunc k)[X] =>
    Function.Bijective (Gal.galActionHom r r.SplittingField)) hgen) h

end Rhone.Algebra.GaloisSpecialization
