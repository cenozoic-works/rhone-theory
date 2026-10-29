/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.GenericGroup
public import Rhone.Algebra.GaloisDegreeSeven.AlgClosed

/-! # Generic symmetric Galois groups for the quintic and septic determinants -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

theorem E55gen_galois_full :
    Function.Bijective (Gal.galActionHom
      (Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ)))
      (Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ))).SplittingField) := by
  apply generic_galois_full_of_specialization Rhone.Algebra.Galois.E55gen (-43 / 5 : ℚ)
  · rw [leadingCoeff, Rhone.Algebra.Galois.E55gen_natDegree, Rhone.Algebra.Galois.E55gen_coeff5]
    norm_num
  · rw [Rhone.Algebra.Galois.E55gen_map_spec]
    exact Rhone.Algebra.Galois.E55pt_irreducible.separable
  · exact Rhone.Algebra.Galois.E55gen_irreducible_ratFunc.separable
  · rw [Rhone.Algebra.Galois.E55gen_map_spec, Rhone.Algebra.Galois.card_gal_E55pt,
      Rhone.Algebra.Galois.E55gen_natDegree]
    norm_num

theorem E77gen_galois_full :
    Function.Bijective (Gal.galActionHom
      (Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ)))
      (Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ))).SplittingField) :=
          by
  apply generic_galois_full_of_specialization Rhone.Algebra.GaloisDegreeSeven.E77gen (-88 / 7 : ℚ)
  · exact Rhone.Algebra.GaloisDegreeSeven.E77gen_lc_spec_ne_zero
  · rw [Rhone.Algebra.GaloisDegreeSeven.E77gen_map_spec]
    exact Rhone.Algebra.GaloisDegreeSeven.E77pt_irreducible.separable
  · exact Rhone.Algebra.GaloisDegreeSeven.E77gen_irreducible_ratFunc.separable
  · rw [Rhone.Algebra.GaloisDegreeSeven.E77gen_map_spec,
      Rhone.Algebra.GaloisDegreeSeven.card_gal_E77pt,
      Rhone.Algebra.GaloisDegreeSeven.natDegree_E77gen]
    norm_num

end Rhone.Algebra.GaloisSpecialization
