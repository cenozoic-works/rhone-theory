/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # The descent step: a `ρ`-factor of a cleared polynomial divides every `π`-coefficient -/

@[expose] public section

namespace Rhone.Algebra.RareAlleleHierarchy

open Polynomial

section Residue

variable {K : Type*} [Field K] {e : Polynomial K}

theorem isMaximal_span_of_irreducible (he : Irreducible e) :
    (Ideal.span ({e} : Set (Polynomial K))).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible he

end Residue

section MvDescent

variable {K : Type*} [Field K] {ι : Type*}

def DvdCleared (e : Polynomial K) (f : MvPolynomial ι (Polynomial K)) : Prop :=
  ∃ (d : MvPolynomial ι K) (g : MvPolynomial ι (Polynomial K)),
    d ≠ 0 ∧
      MvPolynomial.map (Polynomial.C : K →+* Polynomial K) d * f = MvPolynomial.C e * g

theorem dvdCleared_of_dvd {e : Polynomial K} {f : MvPolynomial ι (Polynomial K)}
    (h : MvPolynomial.C e ∣ f) : DvdCleared e f := by
  obtain ⟨g, hg⟩ := h
  exact ⟨1, g, one_ne_zero, by rw [map_one, one_mul, hg]⟩

theorem coeff_dvd_of_dvdCleared {e : Polynomial K} (he : Irreducible e)
    {f : MvPolynomial ι (Polynomial K)} (h : DvdCleared e f) (m : ι →₀ ℕ) :
    e ∣ f.coeff m := by
  classical
  obtain ⟨d, g, hd, hdf⟩ := h
  have : (Ideal.span ({e} : Set (Polynomial K))).IsMaximal :=
    isMaximal_span_of_irreducible he
  let _ : Field (Polynomial K ⧸ Ideal.span ({e} : Set (Polynomial K))) :=
    Ideal.Quotient.field _
  set π := Ideal.Quotient.mk (Ideal.span ({e} : Set (Polynomial K))) with hπ
  have he0 : π e = 0 := by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self e
  have hmap := congrArg (MvPolynomial.map π) hdf
  rw [map_mul, map_mul, MvPolynomial.map_C, he0, MvPolynomial.C_0, zero_mul] at hmap
  have hdne : MvPolynomial.map π
      (MvPolynomial.map (Polynomial.C : K →+* Polynomial K) d) ≠ 0 := by
    rw [MvPolynomial.map_map]
    intro hc
    refine hd (MvPolynomial.map_injective (π.comp (Polynomial.C : K →+* Polynomial K))
      (RingHom.injective _) ?_)
    rw [hc, map_zero]
  have hf0 : MvPolynomial.map π f = 0 := by
    rcases mul_eq_zero.mp hmap with h1 | h1
    · exact absurd h1 hdne
    · exact h1
  have hc := congrArg (fun p => p.coeff m) hf0
  rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hc
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)

end MvDescent

section PolyDescent

variable {K : Type*} [Field K]

def DvdClearedP (e : Polynomial K) (f : Polynomial (Polynomial K)) : Prop :=
  ∃ (d : Polynomial K) (g : Polynomial (Polynomial K)),
    d ≠ 0 ∧ Polynomial.map (Polynomial.C : K →+* Polynomial K) d * f = Polynomial.C e * g

theorem dvdClearedP_of_dvd {e : Polynomial K} {f : Polynomial (Polynomial K)}
    (h : Polynomial.C e ∣ f) : DvdClearedP e f := by
  obtain ⟨g, hg⟩ := h
  exact ⟨1, g, one_ne_zero, by rw [Polynomial.map_one, one_mul, hg]⟩

theorem coeff_dvd_of_dvdClearedP {e : Polynomial K} (he : Irreducible e)
    {f : Polynomial (Polynomial K)} (h : DvdClearedP e f) (n : ℕ) : e ∣ f.coeff n := by
  classical
  obtain ⟨d, g, hd, hdf⟩ := h
  have : (Ideal.span ({e} : Set (Polynomial K))).IsMaximal :=
    isMaximal_span_of_irreducible he
  let _ : Field (Polynomial K ⧸ Ideal.span ({e} : Set (Polynomial K))) :=
    Ideal.Quotient.field _
  set π := Ideal.Quotient.mk (Ideal.span ({e} : Set (Polynomial K))) with hπ
  have he0 : π e = 0 := by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self e
  have hmap := congrArg (Polynomial.map π) hdf
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, he0, Polynomial.C_0,
    zero_mul] at hmap
  have hdne : Polynomial.map π (Polynomial.map (Polynomial.C : K →+* Polynomial K) d) ≠ 0 := by
    rw [Polynomial.map_map]
    intro hc
    refine hd (Polynomial.map_injective (π.comp (Polynomial.C : K →+* Polynomial K))
      (RingHom.injective _) ?_)
    rw [hc, Polynomial.map_zero]
  have hf0 : Polynomial.map π f = 0 := by
    rcases mul_eq_zero.mp hmap with h1 | h1
    · exact absurd h1 hdne
    · exact h1
  have hc := congrArg (fun s => Polynomial.coeff s n) hf0
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hc)

end PolyDescent

section Coprime

variable {K : Type*} [Field K]

theorem isCoprime_of_no_common_irreducible {a b : Polynomial K} (hb : b ≠ 0)
    (h : ∀ e : Polynomial K, Irreducible e → e ∣ a → ¬ e ∣ b) : IsCoprime a b := by
  refine EuclideanDomain.isCoprime_of_dvd (fun hz => hb hz.2) ?_
  intro z hz hz0 hza hzb
  obtain ⟨e, he, hez⟩ := WfDvdMonoid.exists_irreducible_factor hz hz0
  exact h e he (hez.trans hza) (hez.trans hzb)

theorem no_common_irreducible_of_isCoprime {a b : Polynomial K} (h : IsCoprime a b)
    (e : Polynomial K) (he : Irreducible e) (hea : e ∣ a) (heb : e ∣ b) : False :=
  he.not_isUnit (h.isUnit_of_dvd' hea heb)

end Coprime

end Rhone.Algebra.RareAlleleHierarchy
