module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Polynomial.Bivariate

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Rhone.Algebra

open Polynomial

inductive Expr (F : Type*) : Type _
  | const : ℚ → Expr F
  | coeff : F → Expr F
  | thA : Expr F
  | thB : Expr F
  | rho : Expr F
  | add : Expr F → Expr F → Expr F
  | mul : Expr F → Expr F → Expr F
  | div : Expr F → Expr F → Expr F

namespace Expr

variable {F : Type*} [Field F]

noncomputable def eval (tA tB tR : RatFunc F) : Expr F → RatFunc F
  | .const q => (q : RatFunc F)
  | .coeff x => algebraMap F (RatFunc F) x
  | .thA => tA
  | .thB => tB
  | .rho => tR
  | .add x y => eval tA tB tR x + eval tA tB tR y
  | .mul x y => eval tA tB tR x * eval tA tB tR y
  | .div x y => eval tA tB tR x / eval tA tB tR y

end Expr

inductive DAdm {F : Type*} [Field F] (tA tB tR : RatFunc F) (D : ℕ) : Expr F → Prop
  | const (q : ℚ) : DAdm tA tB tR D (.const q)
  | coeff (x : F) : DAdm tA tB tR D (.coeff x)
  | thA : DAdm tA tB tR D .thA
  | thB : DAdm tA tB tR D .thB
  | rho : DAdm tA tB tR D .rho
  | add {x y : Expr F} : DAdm tA tB tR D x → DAdm tA tB tR D y → DAdm tA tB tR D (.add x y)
  | mul {x y : Expr F} : DAdm tA tB tR D x → DAdm tA tB tR D y → DAdm tA tB tR D (.mul x y)
  | div {x g : Expr F} (hx : DAdm tA tB tR D x) (hg : DAdm tA tB tR D g)
      (p : Polynomial F) (hp : p ≠ 0) (hdeg : p.natDegree ≤ D)
      (hval : Expr.eval tA tB tR g = algebraMap (Polynomial F) (RatFunc F) p) :
      DAdm tA tB tR D (.div x g)

clear_aux_proof_cache

section BoundedDenSection

variable {F : Type*} [Field F]

def BoundedDen (D : ℕ) (f : RatFunc F) : Prop :=
  ∃ N M : Polynomial F, M ≠ 0 ∧
    f * algebraMap (Polynomial F) (RatFunc F) M = algebraMap (Polynomial F) (RatFunc F) N ∧
    ∀ p : Polynomial F, Irreducible p → p ∣ M → p.natDegree ≤ D

end BoundedDenSection

end Rhone.Algebra

clear_aux_proof_cache

namespace Rhone.Algebra.GenericField

open Polynomial

abbrev Fv (K : Type*) [Field K] := RatFunc K

abbrev Fuv (K : Type*) [Field K] := RatFunc (Fv K)

abbrev P (K : Type*) [Field K] := Polynomial (Fuv K)

abbrev L (K : Type*) [Field K] := RatFunc (Fuv K)

variable (K : Type*) [Field K]

noncomputable def uu : Fuv K := RatFunc.X

noncomputable def vv : Fuv K := algebraMap (Fv K) (Fuv K) RatFunc.X

noncomputable def thA : L K := algebraMap (Fuv K) (L K) ((uu K + vv K) / 2)

noncomputable def thB : L K := algebraMap (Fuv K) (L K) ((uu K - vv K) / 2)

noncomputable def rhoL : L K := RatFunc.X

clear_aux_proof_cache

noncomputable def coeffHom : K →+* P K :=
  (Polynomial.C).comp ((algebraMap (Fv K) (Fuv K)).comp (algebraMap K (Fv K)))

noncomputable def genRho : Fin 3 → P K :=
  ![C ((uu K + vv K) / 2), C ((uu K - vv K) / 2), X]

noncomputable def evP : MvPolynomial (Fin 3) K →+* P K :=
  MvPolynomial.eval₂Hom (coeffHom K) (genRho K)

noncomputable def evL : MvPolynomial (Fin 3) K →+* L K :=
  (algebraMap (P K) (L K)).comp (evP K)

inductive TotalDAdm (D : ℕ) : Expr (Fuv K) → Prop
  | const (q : ℚ) : TotalDAdm D (.const q)
  | coeff (x : Fuv K) : TotalDAdm D (.coeff x)
  | thA : TotalDAdm D .thA
  | thB : TotalDAdm D .thB
  | rho : TotalDAdm D .rho
  | add {x y : Expr (Fuv K)} : TotalDAdm D x → TotalDAdm D y → TotalDAdm D (.add x y)
  | mul {x y : Expr (Fuv K)} : TotalDAdm D x → TotalDAdm D y → TotalDAdm D (.mul x y)
  | div {x g : Expr (Fuv K)} (hx : TotalDAdm D x) (hg : TotalDAdm D g)
      (m : MvPolynomial (Fin 3) K) (hm : m.totalDegree ≤ D) (hne : evL K m ≠ 0)
      (hval : Expr.eval (_root_.Rhone.Algebra.GenericField.thA K)
          (_root_.Rhone.Algebra.GenericField.thB K)
        (_root_.Rhone.Algebra.GenericField.rhoL K) g = evL K m) :
      TotalDAdm D (.div x g)

end Rhone.Algebra.GenericField

namespace Rhone.Algebra.KilledSystem

structure St where
  a0 : ℕ
  a1 : ℕ
  b0 : ℕ
  b1 : ℕ
  c00 : ℕ
  c01 : ℕ
  c10 : ℕ
  c11 : ℕ
deriving DecidableEq, Repr

namespace St

def t (s : St) : ℕ := s.c00 + s.c01 + s.c10 + s.c11

def nA (s : St) : ℕ := s.a0 + s.a1 + s.t

def nB (s : St) : ℕ := s.b0 + s.b1 + s.t

def n (s : St) : ℕ := s.a0 + s.a1 + s.b0 + s.b1 + s.t

def cr0 (s : St) : ℕ := s.c00 + s.c01

def cr1 (s : St) : ℕ := s.c10 + s.c11

def cc0 (s : St) : ℕ := s.c00 + s.c10

def cc1 (s : St) : ℕ := s.c01 + s.c11

end St

def recStates : List St :=
  [
    ⟨0, 0, 0, 2, 0, 0, 0, 0⟩,
    ⟨0, 0, 1, 1, 0, 0, 0, 0⟩,
    ⟨0, 0, 2, 0, 0, 0, 0, 0⟩,
    ⟨0, 1, 0, 1, 0, 0, 0, 0⟩,
    ⟨0, 1, 1, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 1, 0, 0, 0, 0⟩,
    ⟨1, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨0, 2, 0, 0, 0, 0, 0, 0⟩,
    ⟨1, 1, 0, 0, 0, 0, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 1, 0, 0, 0, 1⟩,
    ⟨0, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨0, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨0, 0, 0, 1, 1, 0, 0, 0⟩,
    ⟨0, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨0, 0, 1, 0, 0, 0, 1, 0⟩,
    ⟨0, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨0, 0, 1, 0, 1, 0, 0, 0⟩,
    ⟨0, 1, 0, 2, 0, 0, 0, 0⟩,
    ⟨0, 1, 1, 1, 0, 0, 0, 0⟩,
    ⟨0, 1, 2, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 2, 0, 0, 0, 0⟩,
    ⟨1, 0, 1, 1, 0, 0, 0, 0⟩,
    ⟨1, 0, 2, 0, 0, 0, 0, 0⟩,
    ⟨0, 1, 0, 0, 0, 0, 0, 1⟩,
    ⟨0, 1, 0, 0, 0, 0, 1, 0⟩,
    ⟨0, 1, 0, 0, 0, 1, 0, 0⟩,
    ⟨0, 1, 0, 0, 1, 0, 0, 0⟩,
    ⟨0, 2, 0, 1, 0, 0, 0, 0⟩,
    ⟨0, 2, 1, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 1, 0, 0, 0⟩,
    ⟨1, 1, 0, 1, 0, 0, 0, 0⟩,
    ⟨1, 1, 1, 0, 0, 0, 0, 0⟩,
    ⟨2, 0, 0, 1, 0, 0, 0, 0⟩,
    ⟨2, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 0, 0, 0, 0, 2⟩,
    ⟨0, 0, 0, 0, 0, 0, 1, 1⟩,
    ⟨0, 0, 0, 0, 0, 0, 2, 0⟩,
    ⟨0, 0, 0, 0, 0, 1, 0, 1⟩,
    ⟨0, 0, 0, 0, 0, 1, 1, 0⟩,
    ⟨0, 0, 0, 0, 0, 2, 0, 0⟩,
    ⟨0, 0, 0, 0, 1, 0, 0, 1⟩,
    ⟨0, 0, 0, 0, 1, 0, 1, 0⟩,
    ⟨0, 0, 0, 0, 1, 1, 0, 0⟩,
    ⟨0, 0, 0, 0, 2, 0, 0, 0⟩,
    ⟨0, 1, 0, 1, 0, 0, 0, 1⟩,
    ⟨0, 1, 0, 1, 0, 0, 1, 0⟩,
    ⟨0, 1, 0, 1, 0, 1, 0, 0⟩,
    ⟨0, 1, 0, 1, 1, 0, 0, 0⟩,
    ⟨0, 1, 1, 0, 0, 0, 0, 1⟩,
    ⟨0, 1, 1, 0, 0, 0, 1, 0⟩,
    ⟨0, 1, 1, 0, 0, 1, 0, 0⟩,
    ⟨0, 1, 1, 0, 1, 0, 0, 0⟩,
    ⟨0, 2, 0, 2, 0, 0, 0, 0⟩,
    ⟨0, 2, 1, 1, 0, 0, 0, 0⟩,
    ⟨0, 2, 2, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 1, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 1, 1, 0, 0, 0⟩,
    ⟨1, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 1, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 1, 0, 1, 0, 0, 0⟩,
    ⟨1, 1, 0, 2, 0, 0, 0, 0⟩,
    ⟨1, 1, 1, 1, 0, 0, 0, 0⟩,
    ⟨1, 1, 2, 0, 0, 0, 0, 0⟩,
    ⟨2, 0, 0, 2, 0, 0, 0, 0⟩,
    ⟨2, 0, 1, 1, 0, 0, 0, 0⟩,
    ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
  ]

def bdryStates : List St :=
  [
    ⟨0, 0, 0, 1, 0, 0, 0, 0⟩,
    ⟨0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨0, 1, 0, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨0, 0, 0, 0, 0, 0, 0, 1⟩,
    ⟨0, 0, 0, 0, 0, 0, 1, 0⟩,
    ⟨0, 0, 0, 0, 0, 1, 0, 0⟩,
    ⟨0, 0, 0, 0, 1, 0, 0, 0⟩
  ]

open St

def rterms (s : St) : List (ℕ × ℕ × St) :=
  [
    (s.a0 * (s.a0 - 1 + 2 * s.cr0), 0, {s with a0 := s.a0 - 1}),
    (s.a1 * (s.a1 - 1 + 2 * s.cr1), 0, {s with a1 := s.a1 - 1}),

    (s.b0 * (s.b0 - 1 + 2 * s.cc0), 0, {s with b0 := s.b0 - 1}),
    (s.b1 * (s.b1 - 1 + 2 * s.cc1), 0, {s with b1 := s.b1 - 1}),

    (s.c00 * (s.c00 - 1), 0, {s with c00 := s.c00 - 1}),
    (s.c01 * (s.c01 - 1), 0, {s with c01 := s.c01 - 1}),
    (s.c10 * (s.c10 - 1), 0, {s with c10 := s.c10 - 1}),
    (s.c11 * (s.c11 - 1), 0, {s with c11 := s.c11 - 1}),

    (2 * s.a0 * s.b0, 0, {s with a0 := s.a0 - 1, b0 := s.b0 - 1, c00 := s.c00 + 1}),
    (2 * s.a0 * s.b1, 0, {s with a0 := s.a0 - 1, b1 := s.b1 - 1, c01 := s.c01 + 1}),
    (2 * s.a1 * s.b0, 0, {s with a1 := s.a1 - 1, b0 := s.b0 - 1, c10 := s.c10 + 1}),
    (2 * s.a1 * s.b1, 0, {s with a1 := s.a1 - 1, b1 := s.b1 - 1, c11 := s.c11 + 1}),

    (s.a0, 1, {s with a0 := s.a0 - 1}),
    (s.c00, 1, {s with b0 := s.b0 + 1, c00 := s.c00 - 1}),
    (s.c01, 1, {s with b1 := s.b1 + 1, c01 := s.c01 - 1}),

    (s.a1, 2, {s with a1 := s.a1 - 1}),
    (s.c10, 2, {s with b0 := s.b0 + 1, c10 := s.c10 - 1}),
    (s.c11, 2, {s with b1 := s.b1 + 1, c11 := s.c11 - 1}),

    (s.b0, 3, {s with b0 := s.b0 - 1}),
    (s.c00, 3, {s with a0 := s.a0 + 1, c00 := s.c00 - 1}),
    (s.c10, 3, {s with a1 := s.a1 + 1, c10 := s.c10 - 1}),

    (s.b1, 4, {s with b1 := s.b1 - 1}),
    (s.c01, 4, {s with a0 := s.a0 + 1, c01 := s.c01 - 1}),
    (s.c11, 4, {s with a1 := s.a1 + 1, c11 := s.c11 - 1}),

    (s.c00, 5, {s with a0 := s.a0 + 1, b0 := s.b0 + 1, c00 := s.c00 - 1}),
    (s.c01, 5, {s with a0 := s.a0 + 1, b1 := s.b1 + 1, c01 := s.c01 - 1}),
    (s.c10, 5, {s with a1 := s.a1 + 1, b0 := s.b0 + 1, c10 := s.c10 - 1}),
    (s.c11, 5, {s with a1 := s.a1 + 1, b1 := s.b1 + 1, c11 := s.c11 - 1}) ]

section Ring

variable {R : Type*} [CommRing R]

def pfac (w0 w1 w2 w3 w4 w5 : R) : ℕ → R
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | 5 => w5
  | _ => 0

def lhsC (tA tB r : R) (s : St) : R :=
  ((s.n * (s.n - 1) : ℕ) : R) + tA * (s.nA : ℕ) + tB * (s.nB : ℕ) + r * (s.t : ℕ)

def rhsC (w0 w1 w2 w3 w4 w5 : R) (q : St → R) (s : St) : R :=
  ((rterms s).map fun x => (x.1 : R) * pfac w0 w1 w2 w3 w4 w5 x.2.1 * q x.2.2).sum

def bdryC (pA0 pA1 pB0 pB1 : R) (s : St) : R :=
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ then pA0
  else if s = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ then pA1
  else if s = ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ then pB0
  else if s = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ then pB1
  else if s = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ then pA0 * pB0
  else if s = ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ then pA0 * pB1
  else if s = ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ then pA1 * pB0
  else if s = ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ then pA1 * pB1
  else 0

end Ring

end Rhone.Algebra.KilledSystem

clear_aux_proof_cache

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

variable (K : Type*) [Field K]

noncomputable def kToFuv : K →+* GenericField.Fuv K :=
  (algebraMap (GenericField.Fv K) (GenericField.Fuv K)).comp (algebraMap K (GenericField.Fv K))

variable {K}

abbrev Kpi : Type := RatFunc (RatFunc ℚ)

noncomputable def piA : Kpi := algebraMap (RatFunc ℚ) Kpi RatFunc.X

noncomputable def piB : Kpi := RatFunc.X

noncomputable def piAF : GenericField.Fuv Kpi := kToFuv Kpi piA

noncomputable def piBF : GenericField.Fuv Kpi := kToFuv Kpi piB

end Rhone.Algebra.SymbolicFrequencies

clear_aux_proof_cache

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

noncomputable def piAL : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      SymbolicFrequencies.piAF

noncomputable def piBL : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      SymbolicFrequencies.piBF

def s22 : St := ⟨0, 0, 0, 0, 0, 0, 0, 2⟩

def IsSolutionG (tA tB r pa pb : GenericField.L SymbolicFrequencies.Kpi)
    (q : St → GenericField.L SymbolicFrequencies.Kpi) : Prop :=
  (∀ s ∈ recStates, lhsC tA tB r s * q s
      = rhsC 1 (tA * pa) (tA * (1 - pa)) (tB * pb) (tB * (1 - pb)) r q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC pa (1 - pa) pb (1 - pb) s)

clear_aux_proof_cache

def IsSolutionπ (q : St → GenericField.L SymbolicFrequencies.Kpi) : Prop :=
  (∀ s ∈ recStates, lhsC (GenericField.thA SymbolicFrequencies.Kpi)
      (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) s * q s
      = rhsC 1 (GenericField.thA SymbolicFrequencies.Kpi * piAL)
          (GenericField.thA SymbolicFrequencies.Kpi * (1 - piAL))
        (GenericField.thB SymbolicFrequencies.Kpi * piBL)
            (GenericField.thB SymbolicFrequencies.Kpi * (1 - piBL))
            (GenericField.rhoL SymbolicFrequencies.Kpi) q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC piAL (1 - piAL) piBL (1 - piBL) s)

clear_aux_proof_cache

noncomputable abbrev rhoMπ : GenericField.Fuv SymbolicFrequencies.Kpi := GenericField.uu
    SymbolicFrequencies.Kpi

clear_aux_proof_cache

noncomputable def tAUπ : GenericField.P SymbolicFrequencies.Kpi := X + C
    (GenericField.vv SymbolicFrequencies.Kpi)

noncomputable def tBUπ : GenericField.P SymbolicFrequencies.Kpi := X - C
    (GenericField.vv SymbolicFrequencies.Kpi)

noncomputable def rhoPUπ : GenericField.P SymbolicFrequencies.Kpi := C rhoMπ

noncomputable def thAuπ : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X + C (GenericField.vv SymbolicFrequencies.Kpi)))

noncomputable def thBuπ : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X - C (GenericField.vv SymbolicFrequencies.Kpi)))

noncomputable def rhoUπ : GenericField.L SymbolicFrequencies.Kpi := algebraMap
    (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi) rhoMπ

clear_aux_proof_cache

noncomputable def coeffHomUπ : SymbolicFrequencies.Kpi →+* GenericField.P SymbolicFrequencies.Kpi :=
  (Polynomial.C).comp
      ((algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi)).comp
    (algebraMap SymbolicFrequencies.Kpi (GenericField.Fv SymbolicFrequencies.Kpi)))

noncomputable def genUπ : Fin 3 → GenericField.P SymbolicFrequencies.Kpi :=
  ![C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
      (X + C (GenericField.vv SymbolicFrequencies.Kpi)),
    C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X - C (GenericField.vv SymbolicFrequencies.Kpi)),
    C rhoMπ]

noncomputable def evPUπ : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi →+* GenericField.P
    SymbolicFrequencies.Kpi :=
  MvPolynomial.eval₂Hom coeffHomUπ genUπ

noncomputable def evLUπ : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi →+* GenericField.L
    SymbolicFrequencies.Kpi :=
  (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi)).comp evPUπ

inductive TotalDAdmUπ (D : ℕ) : Expr (GenericField.Fuv SymbolicFrequencies.Kpi) → Prop
  | const (q : ℚ) : TotalDAdmUπ D (.const q)
  | coeff (x : GenericField.Fuv SymbolicFrequencies.Kpi) : TotalDAdmUπ D (.coeff x)
  | thA : TotalDAdmUπ D .thA
  | thB : TotalDAdmUπ D .thB
  | rho : TotalDAdmUπ D .rho
  | add {x y : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} : TotalDAdmUπ D x → TotalDAdmUπ D
      y →
      TotalDAdmUπ D (.add x y)
  | mul {x y : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} : TotalDAdmUπ D x → TotalDAdmUπ D
      y →
      TotalDAdmUπ D (.mul x y)
  | div {x g : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} (hx : TotalDAdmUπ D x)
      (hg : TotalDAdmUπ D g)
      (m : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi) (hm : m.totalDegree ≤ D)
          (hne : evLUπ m ≠ 0)
      (hval : Expr.eval thAuπ thBuπ rhoUπ g = evLUπ m) :
      TotalDAdmUπ D (.div x g)

end Rhone.Algebra.BlockTwoSymbolic

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.Recursion

open Finset

section ConfigFile

variable {KA KB : ℕ}

def incf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i + 1)

def decf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i - 1)

structure Config (KA KB : ℕ) where

  a : Fin KA → ℕ

  b : Fin KB → ℕ

  c : Fin KA → Fin KB → ℕ

namespace Config

def sumA (ξ : Config KA KB) : ℕ := ∑ i, ξ.a i

def sumB (ξ : Config KA KB) : ℕ := ∑ j, ξ.b j

def t (ξ : Config KA KB) : ℕ := ∑ i, ∑ j, ξ.c i j

def cRow (ξ : Config KA KB) (i : Fin KA) : ℕ := ∑ j, ξ.c i j

def cCol (ξ : Config KA KB) (j : Fin KB) : ℕ := ∑ i, ξ.c i j

def nA (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.t

def nB (ξ : Config KA KB) : ℕ := ξ.sumB + ξ.t

def n (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.sumB + ξ.t

def mA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.a i + ξ.cRow i

def mB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.b j + ξ.cCol j

def incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (incf (m i) j)

def decC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (decf (m i) j)

def dropA (ξ : Config KA KB) (i : Fin KA) : Config KA KB := ⟨decf ξ.a i, ξ.b, ξ.c⟩

def dropB (ξ : Config KA KB) (j : Fin KB) : Config KA KB := ⟨ξ.a, decf ξ.b j, ξ.c⟩

def dropC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, ξ.b, decC ξ.c i j⟩

def mergeAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨decf ξ.a i, decf ξ.b j, incC ξ.c i j⟩

def killA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, incf ξ.b j, decC ξ.c i j⟩

def killB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, ξ.b, decC ξ.c i j⟩

def split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, incf ξ.b j, decC ξ.c i j⟩

instance : Zero (Config KA KB) := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩

def eA (i : Fin KA) : Config KA KB := ⟨incf (fun _ => 0) i, fun _ => 0, fun _ _ => 0⟩

def eB (j : Fin KB) : Config KA KB := ⟨fun _ => 0, incf (fun _ => 0) j, fun _ _ => 0⟩

def eC (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, incC (fun _ _ => 0) i j⟩

end Config

end ConfigFile

section Defs

open Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]

namespace Config

def coalA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.a i * (ξ.a i - 1 + 2 * ξ.cRow i)

def coalB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.b j * (ξ.b j - 1 + 2 * ξ.cCol j)

def coalC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := ξ.c i j * (ξ.c i j - 1)

def coalAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := 2 * (ξ.a i * ξ.b j)

end Config

def diag (θA θB ρ : F) (ξ : Config KA KB) : F :=
  ((ξ.n * (ξ.n - 1) : ℕ) : F) + θA * (ξ.nA : ℕ) + θB * (ξ.nB : ℕ) + ρ * (ξ.t : ℕ)

def rhs (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
    + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j))
    + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j))
    + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

structure IsSolution (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) : Prop where

  empty : q 0 = 1

  bdryA : ∀ i, q (Config.eA i) = πA i

  bdryB : ∀ j, q (Config.eB j) = πB j

  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j

  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n → diag θA θB ρ ξ * q ξ = rhs θA θB ρ πA πB q ξ

end Defs

end Rhone.LinearAlgebra.Recursion

clear_aux_proof_cache

namespace Rhone.Algebra.SamplingUniform

open Polynomial

variable {K : Type*} [Field K]

section NarrowInstances

attribute [-instance] IsDomain.of_isSimpleRing

noncomputable def swapLocal : K[X][X] →+* (RatFunc K)[X] :=
  (Polynomial.mapRingHom (algebraMap K[X] (RatFunc K))).comp
    (Polynomial.Bivariate.swap (R := K)).toRingHom

noncomputable def nestedConstant : K →+* RatFunc (RatFunc (RatFunc K)) :=
  RatFunc.C.comp (RatFunc.C.comp RatFunc.C)

end NarrowInstances

end Rhone.Algebra.SamplingUniform

clear_aux_proof_cache

namespace Rhone.Probability.SamplingUniform

open LinearAlgebra.Recursion

def piOf {R : Type*} [CommRing R] (p : R) : Fin 2 → R := ![p, 1 - p]

def samplingMM (m : ℕ) : Config 2 2 := ⟨![m, 0], ![m, 0], 0⟩

end Rhone.Probability.SamplingUniform

clear_aux_proof_cache

namespace Rhone.Probability.SamplingUniform

open Polynomial

abbrev UniformBase := RatFunc ℚ

abbrev UniformCoefficient := RatFunc (RatFunc (RatFunc UniformBase))

abbrev UniformPolynomial := Polynomial UniformCoefficient

abbrev UniformField := RatFunc UniformCoefficient

noncomputable def uniformLambda : UniformCoefficient :=
  RatFunc.C (RatFunc.C (RatFunc.X : RatFunc UniformBase))

noncomputable def uniformA : UniformField :=
  algebraMap UniformPolynomial UniformField (C uniformLambda)

noncomputable def uniformB : UniformField :=
  algebraMap UniformPolynomial UniformField (X - C uniformLambda)

noncomputable def uniformRho : UniformField :=
  algebraMap UniformPolynomial UniformField
      (C (Algebra.SamplingUniform.nestedConstant (RatFunc.X : UniformBase)))

noncomputable def uniformP : UniformField :=
  algebraMap UniformPolynomial UniformField (C (RatFunc.X : UniformCoefficient))

noncomputable def uniformR : UniformField :=
  algebraMap UniformPolynomial UniformField
    (C (RatFunc.C (RatFunc.X : RatFunc (RatFunc UniformBase))))

end Rhone.Probability.SamplingUniform

clear_aux_proof_cache

namespace Rhone.Probability.RecombinationDegree

open Polynomial Algebra.SamplingUniform

abbrev RecombBase := RatFunc ℚ

abbrev RecombCoefficient := RatFunc (RatFunc (RatFunc RecombBase))

abbrev RecombPolynomial := Polynomial RecombCoefficient

abbrev RecombField := RatFunc RecombCoefficient

noncomputable def recombLambda : RecombCoefficient :=
  RatFunc.C (RatFunc.C (RatFunc.X : RatFunc RecombBase))

noncomputable def recombA : RecombField :=
  algebraMap RecombPolynomial RecombField (C recombLambda)

noncomputable def recombB : RecombField :=
  algebraMap RecombPolynomial RecombField
    (C (nestedConstant (RatFunc.X : RecombBase)) - C recombLambda)

noncomputable def recombRho : RecombField :=
  algebraMap RecombPolynomial RecombField X

noncomputable def recombP : RecombField :=
  algebraMap RecombPolynomial RecombField (C (RatFunc.X : RecombCoefficient))

noncomputable def recombR : RecombField :=
  algebraMap RecombPolynomial RecombField
    (C (RatFunc.C (RatFunc.X : RatFunc (RatFunc RecombBase))))

end Rhone.Probability.RecombinationDegree

clear_aux_proof_cache

namespace Rhone.Palomar.NoEwensFormula

open Rhone.Algebra Rhone.LinearAlgebra Probability Algebra.KilledSystem Algebra.BlockTwoSymbolic

theorem boundedDen_eval {F : Type*} [Field F] {D : ℕ} {tA tB tR : RatFunc F}
    (hA : BoundedDen D tA) (hB : BoundedDen D tB) (hR : BoundedDen D tR)
    {e : Expr F} (h : DAdm tA tB tR D e) : BoundedDen D (Expr.eval tA tB tR e) := by
  sorry

theorem no_degree_one_formula {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      Rhone.Algebra.DAdm (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) 1 e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 := by
  sorry

theorem no_degree_one_formula_total {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), GenericField.TotalDAdm
        SymbolicFrequencies.Kpi 1 e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 := by
  sorry

theorem no_degree_two_formula {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ 2 e ∧
        Expr.eval thAuπ thBuπ rhoUπ e = q s22 := by
  sorry

theorem no_degree_two_formula_total {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), TotalDAdmUπ 2 e
        ∧ Expr.eval thAuπ thBuπ rhoUπ e = q s22 := by
  sorry

theorem exists_isSolutionπ : ∃ q : St → GenericField.L SymbolicFrequencies.Kpi, IsSolutionπ q := by
  sorry

theorem isSolutionπ_unique_s22 {q q' : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q)
    (hq' : IsSolutionπ q') : q s22 = q' s22 := by
  sorry

theorem no_bounded_degree_formula (D : ℕ)
    {q : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rhone.Probability.SamplingUniform.UniformField}
    (hq : Rhone.LinearAlgebra.Recursion.IsSolution
      Rhone.Probability.SamplingUniform.uniformA Rhone.Probability.SamplingUniform.uniformB
      Rhone.Probability.SamplingUniform.uniformRho
      (Rhone.Probability.SamplingUniform.piOf Rhone.Probability.SamplingUniform.uniformP)
      (Rhone.Probability.SamplingUniform.piOf Rhone.Probability.SamplingUniform.uniformR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr
        Rhone.Probability.SamplingUniform.UniformCoefficient,
      Rhone.Algebra.DAdm Rhone.Probability.SamplingUniform.uniformA
        Rhone.Probability.SamplingUniform.uniformB Rhone.Probability.SamplingUniform.uniformRho
        D e ∧
      Rhone.Algebra.Expr.eval Rhone.Probability.SamplingUniform.uniformA
        Rhone.Probability.SamplingUniform.uniformB Rhone.Probability.SamplingUniform.uniformRho
        e = q (Rhone.Probability.SamplingUniform.samplingMM m) := by
  sorry

theorem existsUnique_uniform_solution :
    ∃! q : Rhone.LinearAlgebra.Recursion.Config 2 2 →
        Rhone.Probability.SamplingUniform.UniformField,
      Rhone.LinearAlgebra.Recursion.IsSolution
        Rhone.Probability.SamplingUniform.uniformA Rhone.Probability.SamplingUniform.uniformB
        Rhone.Probability.SamplingUniform.uniformRho
        (Rhone.Probability.SamplingUniform.piOf Rhone.Probability.SamplingUniform.uniformP)
        (Rhone.Probability.SamplingUniform.piOf
          Rhone.Probability.SamplingUniform.uniformR) q := by
  sorry

theorem no_bounded_recombination_degree_formula (D : ℕ)
    {q : Recursion.Config 2 2 → RecombinationDegree.RecombField}
    (hq : Recursion.IsSolution
      RecombinationDegree.recombA RecombinationDegree.recombB
      RecombinationDegree.recombRho
      (SamplingUniform.piOf RecombinationDegree.recombP)
      (SamplingUniform.piOf RecombinationDegree.recombR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Expr RecombinationDegree.RecombCoefficient,
      DAdm RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho D e ∧
      Expr.eval RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho e = q (Rhone.Probability.SamplingUniform.samplingMM m) := by
  sorry

theorem existsUnique_recomb_solution :
    ∃! q : Recursion.Config 2 2 → RecombinationDegree.RecombField,
      Recursion.IsSolution
        RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho
        (SamplingUniform.piOf RecombinationDegree.recombP)
        (SamplingUniform.piOf RecombinationDegree.recombR) q := by
  sorry

end Rhone.Palomar.NoEwensFormula
