/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.Evaluation
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Full generic symmetric groups from a full specialization -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {k : Type*} [Field k]

instance splits_self (p : k[X]) :
    Fact ((p.map (algebraMap k p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

theorem generic_galois_full_of_specialization (p : k[X][X]) (a : k)
    (hlc : (evalRingHom a) p.leadingCoeff ≠ 0)
    (hsep₀ : (p.map (evalRingHom a)).Separable)
    (hsep : (p.map (algebraMap k[X] (RatFunc k))).Separable)
    (hcard : Fintype.card (p.map (evalRingHom a)).Gal = p.natDegree.factorial) :
    Function.Bijective (Gal.galActionHom
      (p.map (algebraMap k[X] (RatFunc k)))
      (p.map (algebraMap k[X] (RatFunc k))).SplittingField) := by
  classical
  let q := p.map (algebraMap k[X] (RatFunc k))
  have : IsGalois (RatFunc k) q.SplittingField :=
    IsGalois.of_separable_splitting_field hsep
  have : IsGaloisGroup q.Gal (RatFunc k) q.SplittingField :=
    IsGaloisGroup.of_isGalois (RatFunc k) q.SplittingField
  obtain ⟨j, hj⟩ := exists_algebra_specialization_embedding
    (K := RatFunc k) (L := q.SplittingField) (G := q.Gal) (aeval a) p hlc hsep₀
  have hbound := Fintype.card_le_of_injective j hj
  have hroots : Fintype.card (q.rootSet q.SplittingField) = p.natDegree := by
    rw [card_rootSet_eq_natDegree hsep (IsSplittingField.splits q.SplittingField q)]
    exact natDegree_map_eq_of_injective (IsFractionRing.injective k[X] (RatFunc k)) p
  have hperm : Fintype.card (Equiv.Perm (q.rootSet q.SplittingField)) =
      p.natDegree.factorial := by rw [Fintype.card_perm, hroots]
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨Gal.galActionHom_injective q q.SplittingField, ?_⟩
  apply le_antisymm (Fintype.card_le_of_injective (Gal.galActionHom q q.SplittingField)
    (Gal.galActionHom_injective q q.SplittingField))
  rw [hperm, ← hcard]
  exact hbound

end Rhone.Algebra.GaloisSpecialization
