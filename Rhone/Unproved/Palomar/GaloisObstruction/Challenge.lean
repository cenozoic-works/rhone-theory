module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

set_option maxSynthPendingDepth 3

@[expose] public section

namespace Rhone.LinearAlgebra.Tridiag

open Matrix

section Basic

variable {R : Type*} [CommRing R]

def tridEntry (d b c : ℕ → R) (s t : ℕ) : R :=
  if t = s then d s else if t = s + 1 then b s else if s = t + 1 then c t else 0

def trid (d b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun s t => tridEntry d b c (s : ℕ) (t : ℕ)

end Basic

section Defs

variable (R : Type*) [CommRing R]

def dcoef (i j : ℕ) (θA θB ρ : R) (t : ℕ) : R :=
  (((i + j - t) * (i + j - t - 1) : ℕ) : R) + θA * i + θB * j + ρ * t

def bcoef (i j : ℕ) (t : ℕ) : R := -2 * (((i - t) * (j - t) : ℕ) : R)

def ccoef (ρ : R) (t : ℕ) : R := -(ρ * ((t : R) + 1))

def T (i j : ℕ) (θA θB ρ : R) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1)

def E (i j : ℕ) (θA θB ρ : R) : R := (T R i j θA θB ρ).det

end Defs

section DL0

variable {F : Type*} [CommRing F]

variable (i j : ℕ) (a b : F)

def kappaT : F := (i : F) * ((i : F) - 1 + a) + (j : F) * ((j : F) - 1 + b)

end DL0

end Rhone.LinearAlgebra.Tridiag

namespace Rhone.Algebra.Galois

open Polynomial LinearAlgebra.Tridiag

def thA55 : ℚ := -9

def thB55 : ℚ := 2 / 5

noncomputable def E55pt : ℚ[X] := E ℚ[X] 5 5 (C thA55) (C thB55) X

noncomputable def E55gen : (Polynomial ℚ)[X] :=
  E ((Polynomial ℚ)[X]) 5 5 (C (Polynomial.X : Polynomial ℚ)) 0 X

end Rhone.Algebra.Galois

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial LinearAlgebra.Tridiag

def thA77 : ℚ := -13

def thB77 : ℚ := 3 / 7

noncomputable def E77pt : ℚ[X] := E ℚ[X] 7 7 (C thA77) (C thB77) X

noncomputable def E77gen : (Polynomial ℚ)[X] :=
  E ((Polynomial ℚ)[X]) 7 7 (C (Polynomial.X : Polynomial ℚ)) 0 X

noncomputable def Epoly (F : Type*) [CommRing F] (i j : ℕ) (θA θB : F) : F[X] :=
  E F[X] i j (C θA) (C θB) X

end Rhone.Algebra.GaloisDegreeSeven

namespace Rhone.Analysis.Rescale

open Polynomial LinearAlgebra.Tridiag

section Laurent

variable {k : Type*} [Field k] [CharZero k]

abbrev LaurentK (k : Type*) [Field k] := FractionRing (PowerSeries k)

noncomputable def sig (k : Type*) [Field k] : LaurentK k :=
  algebraMap (PowerSeries k) (LaurentK k) PowerSeries.X

noncomputable def kToL (k : Type*) [Field k] : k →+* LaurentK k :=
  (algebraMap (PowerSeries k) (LaurentK k)).comp (PowerSeries.C (R := k))

noncomputable def thetaA (k : Type*) [Field k] : LaurentK k := (sig k)⁻¹

noncomputable def thetaB {k : Type*} [Field k] (b : k) : LaurentK k := kToL k b * (sig k)⁻¹

noncomputable def Epoly (i j : ℕ) (b : k) : (LaurentK k)[X] :=
  E (LaurentK k)[X] i j (Polynomial.C (thetaA k)) (Polynomial.C (thetaB b)) Polynomial.X

end Laurent

end Rhone.Analysis.Rescale

namespace Rhone.Analysis.Rescale

open Polynomial

section Witness

noncomputable def qb : FractionRing (Polynomial ℚ) :=
  algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X

end Witness

end Rhone.Analysis.Rescale

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

clear_aux_proof_cache

namespace Rhone.Analysis.GenericCoordinates

section

attribute [-instance] NormMulClass.toNoZeroDivisors

open Polynomial
open LinearAlgebra.Tridiag

abbrev RatioField := FractionRing (Polynomial ℚ)
abbrev GenericField := FractionRing (Polynomial RatioField)

noncomputable def ratio : RatioField := Rhone.Analysis.Rescale.qb

noncomputable def sigmaVariable : GenericField :=
  algebraMap (Polynomial RatioField) GenericField X

noncomputable def ratioIn : GenericField :=
  algebraMap (Polynomial RatioField) GenericField (C ratio)

noncomputable def thetaA : GenericField := sigmaVariable⁻¹
noncomputable def thetaB : GenericField := ratioIn * sigmaVariable⁻¹

end

end Rhone.Analysis.GenericCoordinates

clear_aux_proof_cache

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

section SplitsSelf

variable {k : Type*} [Field k]

instance splits_self (p : k[X]) :
    Fact ((p.map (algebraMap k p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

end SplitsSelf

open LinearAlgebra.Tridiag

abbrev MutationField := RatFunc (RatFunc ℚ)

noncomputable def sumParameter : MutationField := algebraMap (RatFunc ℚ) MutationField RatFunc.X
noncomputable def differenceParameter : MutationField := RatFunc.X
noncomputable def thetaA : MutationField := (sumParameter + differenceParameter) / 2
noncomputable def thetaB : MutationField := (sumParameter - differenceParameter) / 2

end Rhone.Algebra.GaloisSpecialization

namespace Rhone.Palomar.GaloisObstruction

open Polynomial Rhone.Algebra Analysis Rhone.LinearAlgebra LinearAlgebra.Tridiag Analysis.Rescale

theorem natDegree_E {F : Type*} [CommRing F] (i j : ℕ) (a b : F)
    (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j := by
  sorry

theorem E_pos {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F] {i j : ℕ}
    {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    0 < E F i j θA θB ρ := by
  sorry

theorem E55pt_irreducible : Irreducible Galois.E55pt := by
  sorry

theorem card_rootSet_E55pt_real : Fintype.card (Galois.E55pt.rootSet ℝ) = 3 := by
  sorry

theorem card_gal_E55pt : Fintype.card Galois.E55pt.Gal = 120 := by
  sorry

theorem E55pt_root_not_solvableByRad (z : ℂ) (hz : aeval z Galois.E55pt = 0) :
    z ∉ solvableByRad ℚ ℂ := by
  sorry

theorem E77pt_irreducible : Irreducible GaloisDegreeSeven.E77pt := by
  sorry

theorem card_rootSet_E77pt_real : Fintype.card (GaloisDegreeSeven.E77pt.rootSet ℝ) = 5 := by
  sorry

theorem card_gal_E77pt : Fintype.card GaloisDegreeSeven.E77pt.Gal = 5040 := by
  sorry

theorem E77pt_root_not_solvableByRad (z : ℂ) (hz : aeval z GaloisDegreeSeven.E77pt = 0) :
    z ∉ solvableByRad ℚ ℂ := by
  sorry

theorem E55gen_irreducible_ratFunc :
    Irreducible (Galois.E55gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) := by
  sorry

theorem E55gen_irreducible_two_var :
    Irreducible (((Rhone.Algebra.Galois.E55gen.map
        (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) := by
  sorry

theorem E77gen_irreducible_ratFunc :
    Irreducible (GaloisDegreeSeven.E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) := by
  sorry

theorem E77gen_irreducible_two_var :
    Irreducible (((GaloisDegreeSeven.E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) := by
  sorry

theorem E55_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).Splits := by
  sorry

theorem card_roots_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).roots = 5 := by
  sorry

theorem roots_neg_E55 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (GaloisDegreeSeven.Epoly ℝ 5 5 θA θB).roots) :
    x < 0 := by
  sorry

theorem E77_splits (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).Splits := by
  sorry

theorem card_roots_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) :
    Multiset.card (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).roots = 7 := by
  sorry

theorem roots_neg_E77 (θA θB : ℝ) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (x : ℝ)
    (hx : x ∈ (GaloisDegreeSeven.Epoly ℝ 7 7 θA θB).roots) :
    x < 0 := by
  sorry

theorem E_squarefree_laurent {k : Type*} [Field k] [CharZero k] (i j : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0) (hi : 1 ≤ i) :
    Squarefree (Epoly i j b) := by
  sorry

theorem E_coprime_of_ne_laurent {k : Type*} [Field k] [CharZero k] (i j p q : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (hi : 1 ≤ i) (_hj : 1 ≤ j) (hp : 1 ≤ p) (_hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (Epoly i j b) (Epoly p q b) := by
  sorry

theorem E_squarefree_generic (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Squarefree (E GenericCoordinates.GenericField[X] i j
      (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X) := by
  sorry

theorem E_coprime_generic (i j p q : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (E GenericCoordinates.GenericField[X] i j
        (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X)
      (E GenericCoordinates.GenericField[X] p q
        (C GenericCoordinates.thetaA) (C GenericCoordinates.thetaB) X) := by
  sorry

theorem E55_galois_full :
    Function.Bijective (Gal.galActionHom
      (E GaloisSpecialization.MutationField[X] 5 5
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB) X)
      (E GaloisSpecialization.MutationField[X] 5 5
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB)
        X).SplittingField) := by
  sorry

theorem E77_galois_full :
    Function.Bijective (Gal.galActionHom
      (E GaloisSpecialization.MutationField[X] 7 7
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB) X)
      (E GaloisSpecialization.MutationField[X] 7 7
        (C GaloisSpecialization.thetaA) (C GaloisSpecialization.thetaB)
        X).SplittingField) := by
  sorry

theorem generic_galois_full_of_specialization {k : Type*} [Field k] (p : k[X][X]) (a : k)
    (hlc : (evalRingHom a) p.leadingCoeff ≠ 0)
    (hsep₀ : (p.map (evalRingHom a)).Separable)
    (hsep : (p.map (algebraMap k[X] (RatFunc k))).Separable)
    (hcard : Fintype.card (p.map (evalRingHom a)).Gal = p.natDegree.factorial) :
    Function.Bijective (Gal.galActionHom
      (p.map (algebraMap k[X] (RatFunc k)))
      (p.map (algebraMap k[X] (RatFunc k))).SplittingField) := by
  sorry

end Rhone.Palomar.GaloisObstruction
