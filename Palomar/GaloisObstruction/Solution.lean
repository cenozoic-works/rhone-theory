module

public import Rhone.LinearAlgebra.Tridiag.RhoDegree
public import Rhone.Algebra.Galois.E55
public import Rhone.Algebra.GaloisDegreeSeven.E77
public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive
public import Rhone.Algebra.GaloisDegreeSeven.AlgClosed
public import Rhone.Algebra.GaloisDegreeSeven.AllReal
public import Rhone.Analysis.Rescale.Discharge
public import Rhone.Analysis.GenericCoordinates.GenericField
public import Rhone.Algebra.GaloisSpecialization.TwoParameter

@[expose] public section

namespace Rhone.Palomar.GaloisObstruction

open Polynomial Rhone.Algebra Analysis Rhone.LinearAlgebra LinearAlgebra.Tridiag Analysis.Rescale

theorem natDegree_E {F : Type*} [CommRing F] (i j : ℕ) (a b : F)
    (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j :=
  Tridiag.natDegree_E i j a b h

theorem E_pos {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F] {i j : ℕ}
    {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    0 < E F i j θA θB ρ :=
  GaloisDegreeSeven.E_pos hi hj hA hB hρ

theorem E55pt_irreducible : Irreducible Galois.E55pt :=
  Galois.E55pt_irreducible

theorem card_rootSet_E55pt_real : Fintype.card (Galois.E55pt.rootSet ℝ) = 3 :=
  Galois.card_rootSet_E55pt_real

theorem card_gal_E55pt : Fintype.card Galois.E55pt.Gal = 120 :=
  Galois.card_gal_E55pt

theorem E55pt_root_not_solvableByRad (z : ℂ) (hz : aeval z Galois.E55pt = 0) :
    z ∉ solvableByRad ℚ ℂ :=
  Galois.E55pt_root_not_solvableByRad z hz

theorem E77pt_irreducible : Irreducible GaloisDegreeSeven.E77pt :=
  GaloisDegreeSeven.E77pt_irreducible

theorem card_rootSet_E77pt_real : Fintype.card (GaloisDegreeSeven.E77pt.rootSet ℝ) = 5 :=
  GaloisDegreeSeven.card_rootSet_E77pt_real

theorem card_gal_E77pt : Fintype.card GaloisDegreeSeven.E77pt.Gal = 5040 :=
  GaloisDegreeSeven.card_gal_E77pt

theorem E77pt_root_not_solvableByRad (z : ℂ) (hz : aeval z GaloisDegreeSeven.E77pt = 0) :
    z ∉ solvableByRad ℚ ℂ :=
  GaloisDegreeSeven.E77pt_root_not_solvableByRad z hz

theorem E55gen_irreducible_ratFunc :
    Irreducible (Galois.E55gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) :=
  Galois.E55gen_irreducible_ratFunc

theorem E55gen_irreducible_two_var :
    Irreducible (((Rhone.Algebra.Galois.E55gen.map
        (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) :=
  GaloisDegreeSeven.E55gen_irreducible_two_var

theorem E77gen_irreducible_ratFunc :
    Irreducible (GaloisDegreeSeven.E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) :=
  GaloisDegreeSeven.E77gen_irreducible_ratFunc

theorem E77gen_irreducible_two_var :
    Irreducible (((GaloisDegreeSeven.E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) :=
  GaloisDegreeSeven.E77gen_irreducible_two_var

theorem E55_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).Splits :=
  GaloisDegreeSeven.E55_splits θA θB hA hB

theorem card_roots_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).roots = 5 :=
  GaloisDegreeSeven.card_roots_E55 θA θB hA hB

theorem roots_neg_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).roots) :
    x < 0 :=
  GaloisDegreeSeven.roots_neg_E55 θA θB hA hB x hx

theorem E77_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).Splits :=
  GaloisDegreeSeven.E77_splits θA θB hA hB

theorem card_roots_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).roots = 7 :=
  GaloisDegreeSeven.card_roots_E77 θA θB hA hB

theorem roots_neg_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).roots) :
    x < 0 :=
  GaloisDegreeSeven.roots_neg_E77 θA θB hA hB x hx

theorem E_squarefree_laurent {k : Type*} [Field k] [CharZero k] (i j : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0) (hi : 1 ≤ i) :
    Squarefree (Epoly i j b) :=
  Rescale.E_squarefree_laurent i j b hb hi

theorem E_coprime_of_ne_laurent {k : Type*} [Field k] [CharZero k] (i j p q : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (hi : 1 ≤ i) (_hj : 1 ≤ j) (hp : 1 ≤ p) (_hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (Epoly i j b) (Epoly p q b) :=
  Rescale.E_coprime_of_ne_laurent i j p q b hb hi _hj hp _hq hne

theorem E_squarefree_generic (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Squarefree (E GenericCoordinates.GenericField[X] i j
      (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X) :=
  GenericCoordinates.E_squarefree_generic i j hi hj

theorem E_coprime_generic (i j p q : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (E GenericCoordinates.GenericField[X] i j
        (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X)
      (E GenericCoordinates.GenericField[X] p q
        (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X) :=
  GenericCoordinates.E_coprime_generic i j p q hi hj hp hq hne

theorem E55_galois_full :
    Function.Bijective (Gal.galActionHom
      (E GaloisSpecialization.MutationField[X] 5 5
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB) X)
      (E GaloisSpecialization.MutationField[X] 5 5
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB)
        X).SplittingField) :=
  GaloisSpecialization.E55_galois_full

theorem E77_galois_full :
    Function.Bijective (Gal.galActionHom
      (E GaloisSpecialization.MutationField[X] 7 7
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB) X)
      (E GaloisSpecialization.MutationField[X] 7 7
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB)
        X).SplittingField) :=
  GaloisSpecialization.E77_galois_full

theorem generic_galois_full_of_specialization {k : Type*} [Field k] (p : k[X][X]) (a : k)
    (hlc : (evalRingHom a) p.leadingCoeff ≠ 0)
    (hsep₀ : (p.map (evalRingHom a)).Separable)
    (hsep : (p.map (algebraMap k[X] (RatFunc k))).Separable)
    (hcard : Fintype.card (p.map (evalRingHom a)).Gal = p.natDegree.factorial) :
    Function.Bijective (Gal.galActionHom
      (p.map (algebraMap k[X] (RatFunc k)))
      (p.map (algebraMap k[X] (RatFunc k))).SplittingField) :=
  GaloisSpecialization.generic_galois_full_of_specialization p a hlc hsep₀ hsep hcard

end Rhone.Palomar.GaloisObstruction
