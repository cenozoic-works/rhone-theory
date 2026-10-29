/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Reduction

/-! # The abstract diagonal-chain criterion has no converse -/

@[expose] public section

namespace Rhone.Probability.DiagonalChainConverse

open Polynomial Algebra.RareAlleleHierarchy RareAlleleHierarchy

noncomputable def witness : Polynomial (Polynomial ℚ) := C X * X + 1

theorem witness_coeff : witness.coeff 1 = (1 : Polynomial ℚ) * X := by
  simp [witness, coeff_one]

theorem witness_coprime : CoprimeClearedP witness (X : Polynomial ℚ) := by
  intro e he _ hdvd
  have h := coeff_dvd_of_dvdClearedP he hdvd 0
  have he1 : e ∣ (1 : Polynomial ℚ) := by simpa [witness] using h
  exact he.not_isUnit (isUnit_of_dvd_one he1)

theorem witness_not_chain : ¬ IsCoprime (X : Polynomial ℚ) X := by
  intro h
  exact Polynomial.not_isUnit_X (h.isUnit_of_dvd dvd_rfl)

theorem not_criterion_of_diagChain_converse :
    ¬ (∀ (E Dclc ellv : Polynomial ℚ) (f : Polynomial (Polynomial ℚ)) (n : ℕ),
      f.coeff n = Dclc * ellv → IsCoprime Dclc E →
      CoprimeClearedP f E → IsCoprime ellv E) := by
  intro h
  exact witness_not_chain (h X 1 X witness 1 witness_coeff isCoprime_one_left witness_coprime)

end Rhone.Probability.DiagonalChainConverse
