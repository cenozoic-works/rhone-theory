/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Lambda
public import Rhone.Probability.RareAlleleHierarchy.Reduction

/-! # The block `(2,2)`: `ℓ · S^{2,2} = 32 + (α² + β²) W` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial

section Unit

variable {K : Type*} [Field K] {ι : Type*}

theorem coprimeCleared_of_isUnit_coeff {f : MvPolynomial ι (Polynomial K)} (m : ι →₀ ℕ)
    (hu : IsUnit (f.coeff m)) (e : Polynomial K) (he : Irreducible e) :
    ¬ Algebra.RareAlleleHierarchy.DvdCleared e f := by
  intro hdvd
  exact he.not_isUnit
      (isUnit_of_dvd_unit (Algebra.RareAlleleHierarchy.coeff_dvd_of_dvdCleared he hdvd m) hu)

theorem coprimeClearedP_of_isUnit_coeff {f : Polynomial (Polynomial K)} (n : ℕ)
    (hu : IsUnit (f.coeff n)) (e : Polynomial K) (he : Irreducible e) : ¬
        Algebra.RareAlleleHierarchy.DvdClearedP e f := by
  intro hdvd
  exact he.not_isUnit
      (isUnit_of_dvd_unit (Algebra.RareAlleleHierarchy.coeff_dvd_of_dvdClearedP he hdvd n) hu)

end Unit

section Block

variable {K : Type*} [CommRing K] {α β : ℕ → K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem redSource_two_two (t : ℕ) :
    redSource α β Φ 2 2 t
      = (((2 - t) * (2 + t - 1) : ℕ) : K) * (α 2 + β 2) + ((t * (t - 1) : ℕ) : K) := by
  rw [redSource, Theta_one_right α β Φ (le_refl 2), Theta_one_left α β Φ (le_refl 2),
    Theta_one_one]
  ring

theorem ell_dot_redSource_two_two (θA θB ρ : K) :
    (∑ s : Fin (min 2 2 + 1), ell 2 2 θA θB ρ (s : ℕ) * redSource α β Φ 2 2 (s : ℕ))
      = 2 * (α 2 + β 2) * (ell 2 2 θA θB ρ 0 + ell 2 2 θA θB ρ 1) + 32 := by
  change (∑ s : Fin 3, ell 2 2 θA θB ρ (s : ℕ) * redSource α β Φ 2 2 (s : ℕ))
      = 2 * (α 2 + β 2) * (ell 2 2 θA θB ρ 0 + ell 2 2 θA θB ρ 1) + 32
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, redSource_two_two, ell_two_two_top]
  norm_num
  ring

end Block

section Chain2

variable {K : Type*} [Field K] [CharZero K]

theorem isUnit_C_thirtytwo : IsUnit (Polynomial.C (32 : K)) :=
  isUnit_C_of_ne_zero (by norm_num)

theorem chain_criterion_two (E : Polynomial K) : IsCoprime (Polynomial.C (32 : K)) E :=
  isCoprime_of_isUnit_left isUnit_C_thirtytwo

theorem criterion_two_two_of_lead {E Dclc : Polynomial K} {hatΘ₀ : Polynomial (Polynomial K)}
    (n : ℕ) (hlead : hatΘ₀.coeff n = Dclc * Polynomial.C (32 : K))
    (hDclc : IsCoprime Dclc E) : CoprimeClearedP hatΘ₀ E :=
  criterion_of_diagChain n hlead hDclc (chain_criterion_two E)

end Chain2

end Rhone.Probability.RareAlleleHierarchy
