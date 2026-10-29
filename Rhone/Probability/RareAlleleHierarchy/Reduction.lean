/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RareAlleleHierarchy.Descent
public import Rhone.Probability.RareAlleleHierarchy.Coeff

/-! # Two one-directional reductions of the coprime-clearing criterion to a leading term -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial

section Criterion

variable {K : Type*} [Field K]

def CoprimeCleared (f : MvPolynomial (Fin 2) (Polynomial K)) (E : Polynomial K) : Prop :=
  ∀ e : Polynomial K, Irreducible e → e ∣ E → ¬ Algebra.RareAlleleHierarchy.DvdCleared e f

def CoprimeClearedP (f : Polynomial (Polynomial K)) (E : Polynomial K) : Prop :=
  ∀ e : Polynomial K, Irreducible e → e ∣ E → ¬ Algebra.RareAlleleHierarchy.DvdClearedP e f

theorem criterion_of_reduced {E Dcut hatΘ₀ : Polynomial K}
    {hatΦ₀ : MvPolynomial (Fin 2) (Polynomial K)}
    (hcoeff : hatΦ₀.coeff (mon 1 1) = Dcut * hatΘ₀)
    (hDcut : IsCoprime Dcut E) (hred : IsCoprime hatΘ₀ E) :
    CoprimeCleared hatΦ₀ E := by
  intro e he heE hdvd
  have hcf : e ∣ hatΦ₀.coeff (mon 1 1) :=
    Algebra.RareAlleleHierarchy.coeff_dvd_of_dvdCleared he hdvd (mon 1 1)
  rw [hcoeff] at hcf
  rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp he).2.2 _ _ hcf with h1 | h1
  · exact Algebra.RareAlleleHierarchy.no_common_irreducible_of_isCoprime hDcut e he h1 heE
  · exact Algebra.RareAlleleHierarchy.no_common_irreducible_of_isCoprime hred e he h1 heE

theorem criterion_of_diagChain {E Dclc ellv : Polynomial K}
    {hatΘ₀ : Polynomial (Polynomial K)} (n : ℕ)
    (hlead : hatΘ₀.coeff n = Dclc * ellv)
    (hDcut : IsCoprime Dclc E) (hchain : IsCoprime ellv E) :
    CoprimeClearedP hatΘ₀ E := by
  intro e he heE hdvd
  have hcf : e ∣ hatΘ₀.coeff n := Algebra.RareAlleleHierarchy.coeff_dvd_of_dvdClearedP he hdvd n
  rw [hlead] at hcf
  rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp he).2.2 _ _ hcf with h1 | h1
  · exact Algebra.RareAlleleHierarchy.no_common_irreducible_of_isCoprime hDcut e he h1 heE
  · exact Algebra.RareAlleleHierarchy.no_common_irreducible_of_isCoprime hchain e he h1 heE

theorem isCoprime_of_isUnit_left {a b : Polynomial K} (h : IsUnit a) : IsCoprime a b := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨(↑u⁻¹ : Polynomial K), 0, by simp⟩

theorem isUnit_C_of_ne_zero {c : K} (hc : c ≠ 0) : IsUnit (Polynomial.C c) :=
  Polynomial.isUnit_C.mpr hc.isUnit

end Criterion

end Rhone.Probability.RareAlleleHierarchy
