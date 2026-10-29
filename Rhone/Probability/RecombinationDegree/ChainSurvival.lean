/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.VariableExchange
public import Rhone.Probability.DiagonalObstruction.DistinguishedPole

/-! # Distinguished factors survive in the diagonal chain after exchanging variables -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial Algebra.DiagonalObstruction Analysis.DiagonalObstruction DiagonalObstruction

attribute [local instance] Polynomial.algebra

noncomputable def recombinationChainNumerator (m : ℕ) : Polynomial (RatFunc ℚ) :=
  (Polynomial.Bivariate.swap (spectralChainNumerator m)).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ))

theorem recombinationFactor_not_dvd_chain {m : ℕ} (hm : 2 ≤ m)
    (F : Polynomial (Polynomial ℤ)) (hmon : F.Monic) (hz : 0 ∈ factorLabels m F)
    (hi : Irreducible (rationalFunctionFactor F)) (hd : 0 < (coordinates ℤ F).degreeOf 1) :
    ¬ recombinationFactor F ∣ recombinationChainNumerator m := by
  have hq : Irreducible (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) :=
    ((hmon.map _).irreducible_iff_irreducible_map_fraction_map).mpr hi
  have hs : Irreducible
      (Polynomial.Bivariate.swap (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))) :=
    (MulEquiv.irreducible_iff Polynomial.Bivariate.swap).mpr hq
  have hn : (Polynomial.Bivariate.swap
      (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))).natDegree ≠ 0 := by
    rw [rational_swap_natDegree]
    omega
  intro h
  have hb := (hs.isPrimitive hn).dvd_of_fraction_map_dvd_fraction_map h
  exact distinguishedFactor_not_dvd_chain hm F hz
    ((map_dvd_iff Polynomial.Bivariate.swap).mp hb)

theorem unbounded_surviving_recombination_chain_factor (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ F : Polynomial (Polynomial ℤ),
      Irreducible (recombinationFactor F) ∧
      recombinationFactor F ∣ recombinationFactor (spectralPolynomial m) ∧
      ¬ recombinationFactor F ∣ recombinationChainNumerator m ∧
      D < (recombinationFactor F).natDegree := by
  obtain ⟨m, F, hm, hmon, hdiv, hzero, hirr, hdeg⟩ :=
    unbounded_distinguished_recombination_degree D
  refine ⟨m, hm, F, recombinationFactor_irreducible F hmon hirr (by omega), ?_,
    recombinationFactor_not_dvd_chain hm F hmon hzero hirr (by omega), ?_⟩
  · exact Polynomial.map_dvd _ (map_dvd Polynomial.Bivariate.swap.toRingHom
      (Polynomial.map_dvd _ hdiv))
  · rwa [recombinationFactor_natDegree]

end Rhone.Probability.RecombinationDegree
