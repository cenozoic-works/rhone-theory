module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Rhone.LinearAlgebra.Tridiag

open Matrix

section Basic

variable {R : Type*} [CommRing R]

def tridEntry (d b c : ℕ → R) (s t : ℕ) : R :=
  if t = s then d s else if t = s + 1 then b s else if s = t + 1 then c t else 0

def trid (d b c : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun s t => tridEntry d b c (s : ℕ) (t : ℕ)

def tridFrom (d b c : ℕ → R) (s n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun p q => tridEntry d b c ((p : ℕ) + s) ((q : ℕ) + s)

def cont (d b c : ℕ → R) : ℕ → R
  | 0 => 1
  | 1 => d 0
  | (r + 2) => d (r + 1) * cont d b c (r + 1) - b r * c r * cont d b c r

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

end Rhone.LinearAlgebra.Tridiag

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.RecombinationExpansion

open Matrix Tridiag

variable {R : Type*} [CommRing R]

def Qc (d b c : ℕ → R) (n s : ℕ) : R :=
  if s ≤ n then (tridFrom d b c s (n - s)).det else 0

def runProd (f : ℕ → R) (lo hi : ℕ) : R := ∏ s ∈ Finset.Ico lo hi, f s

def usmaniEntry (d b c : ℕ → R) (n i j : ℕ) : R :=
  if i ≤ j then (-1) ^ (i + j) * runProd b i j * cont d b c i * Qc d b c n (j + 1)
  else (-1) ^ (i + j) * runProd c j i * cont d b c j * Qc d b c n (i + 1)

end Rhone.LinearAlgebra.RecombinationExpansion

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.Recursion

open Finset

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

end Rhone.LinearAlgebra.Recursion

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

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

end Rhone.LinearAlgebra.Recursion

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

variable {F : Type*} [Field F]

section Biallelic

variable (π : Fin 2 → F)

def fvec : Fin 2 → F := Pi.single 0 1 - (π 0) • 1

def kap : F := π 0 * π 1

def gam : F := π 1 - π 0

end Biallelic

end Rhone.Probability.Multilinear

namespace Rhone.Probability.SlotDeletion

section Eps

variable {F : Type*} [Field F]

def eps (F : Type*) [Field F] : Fin 2 → F := ![1, -1]

end Eps

end Rhone.Probability.SlotDeletion

clear_aux_proof_cache

namespace Rhone.Probability.Closure

open Finset LinearAlgebra.Recursion Multilinear SlotDeletion

variable {F : Type*} [Field F]

noncomputable def gA (πA : Fin 2 → F) (i : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πA i) + MvPolynomial.C (eps F i) * MvPolynomial.X 0

noncomputable def gB (πB : Fin 2 → F) (j : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πB j) + MvPolynomial.C (eps F j) * MvPolynomial.X 1

noncomputable def gAB (πA πB : Fin 2 → F) (i j : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πA i * πB j)
    + MvPolynomial.C (eps F i * πB j) * MvPolynomial.X 0
    + MvPolynomial.C (πA i * eps F j) * MvPolynomial.X 1
    + MvPolynomial.C (eps F i * eps F j)
        * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

noncomputable def Gcfg (πA πB : Fin 2 → F) (ξ : Config 2 2) : MvPolynomial (Fin 3) F :=
  (∏ i, gA πA i ^ ξ.a i) * (∏ j, gB πB j ^ ξ.b j) * ∏ i, ∏ j, gAB πA πB i j ^ ξ.c i j

end Rhone.Probability.Closure

clear_aux_proof_cache

namespace Rhone.Probability.Closure

noncomputable def mono3 (d1 d2 d3 : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 d1 + Finsupp.single 1 d2 + Finsupp.single 2 d3

end Rhone.Probability.Closure

clear_aux_proof_cache

namespace Rhone.Probability.ExplicitFormula

open Finset LinearAlgebra.Recursion Multilinear Closure

variable {F : Type*} [Field F]

noncomputable def srcR (κA γA κB γB : F) (Ψ : ℕ → ℕ → ℕ → F) (i j t : ℕ) : F :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : F) * Ψ (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : F) * Ψ (i - 2) j (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : F) * Ψ (i - 1) j t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : F) * Ψ i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : F) * Ψ i (j - 2) (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : F) * Ψ i (j - 1) t
    + ((t * (t - 1) : ℕ) : F) * (κA * κB * Ψ (i - 2) (j - 2) (t - 2)
      + κA * γB * Ψ (i - 2) (j - 1) (t - 2)
      + γA * κB * Ψ (i - 1) (j - 2) (t - 2)
      + γA * γB * Ψ (i - 1) (j - 1) (t - 1))

noncomputable def PhiTab (θA θB ρ : F) (πA πB : Fin 2 → F) : ℕ → ℕ → ℕ → ℕ → F
  | 0,   _, _, _ => 1
  | n+1, i, j, t =>
    if i = 0 ∧ j = 0 then 1 else
      (LinearAlgebra.Tridiag.E F i j θA θB ρ)⁻¹ *
        ∑ s ∈ Finset.range (min i j + 1),
          LinearAlgebra.RecombinationExpansion.usmaniEntry
              (LinearAlgebra.Tridiag.dcoef F i j θA θB ρ) (LinearAlgebra.Tridiag.bcoef F i j)
              (LinearAlgebra.Tridiag.ccoef F ρ) (min i j + 1) (min t (min i j)) s
            * srcR (kap πA) (gam πA) (kap πB) (gam πB) (PhiTab θA θB ρ πA πB n) i j s

noncomputable def PhiX (θA θB ρ : F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  PhiTab θA θB ρ πA πB (i + j) i j t

noncomputable def qExplicit (θA θB ρ : F) (πA πB : Fin 2 → F) (ξ : Config 2 2) : F :=
  ∑ d1 ∈ Finset.range (ξ.nA + 1), ∑ d2 ∈ Finset.range (ξ.nB + 1),
    ∑ d3 ∈ Finset.range (ξ.t + 1),
      (Gcfg πA πB ξ).coeff (mono3 d1 d2 d3) * PhiX θA θB ρ πA πB d1 d2 d3

end Rhone.Probability.ExplicitFormula

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Recursion

variable {KA KB KA' KB' : ℕ}

def pushV {K K' : ℕ} (f : Fin K → Fin K') (v : Fin K → ℕ) : Fin K' → ℕ :=
  fun p => ∑ i with f i = p, v i

def pushM (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (m : Fin KA → Fin KB → ℕ) :
    Fin KA' → Fin KB' → ℕ :=
  fun p r => ∑ i with fA i = p, ∑ j with fB j = r, m i j

def push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) : Config KA' KB' :=
  ⟨pushV fA ξ.a, pushV fB ξ.b, pushM fA fB ξ.c⟩

def pushPi {F : Type*} [AddCommMonoid F] {K K' : ℕ} (f : Fin K → Fin K') (π : Fin K → F) :
    Fin K' → F :=
  fun p => ∑ i with f i = p, π i

def mult (ξ : Config KA KB) : ℕ :=
  Nat.multinomial univ ξ.a * Nat.multinomial univ ξ.b
    * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2)

end Rhone.LinearAlgebra.AlleleLumping

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset

variable {F : Type*} [CommRing F] {i : ℕ}

def D : Module.End F (Finset (Fin i) → F) where
  toFun f S := ∑ x ∈ S, f (S.erase x)
  map_add' f g := by
    funext S
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp [Finset.mul_sum]

def U : Module.End F (Finset (Fin i) → F) where
  toFun f S := ∑ x ∈ Sᶜ, f (insert x S)
  map_add' f g := by
    funext S
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp [Finset.mul_sum]

def lev (t : ℕ) (f : Finset (Fin i) → F) : Finset (Fin i) → F :=
  fun S => if S.card = t then f S else 0

end Rhone.LinearAlgebra.BooleanLatticeInverse

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset
open scoped Nat

attribute [-instance] NonUnitalNonAssocSemiring.toDistribSMul

variable {F : Type*} [Field F] {i : ℕ}

def projCoef (F : Type*) [Field F] (M l : ℕ) : F :=
  (-1) ^ l * ((M + 1)! : F) / ((l ! : F) * ((M + l + 1)! : F))

def proj (k t : ℕ) : Module.End F (Finset (Fin i) → F) :=
  (((i - 2 * k - (t - k))! : F) / (((t - k)! : F) * ((i - 2 * k)! : F))) •
    ∑ l ∈ range (k + 1), projCoef F (i - 2 * k) l • (D ^ l * U ^ (l + (t - k)))

end Rhone.LinearAlgebra.BooleanLatticeInverse

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Matrix Tridiag RecombinationExpansion

variable {F : Type*} [Field F]

def sig (i j k : ℕ) : ℕ := min (i - 2 * k) (j - k)

def dK (θA θB ρ : F) (i j k s : ℕ) : F := dcoef F i j θA θB ρ (k + s)

def bK (F : Type*) [Field F] (i j k s : ℕ) : F :=
  -2 * (((j - k - s) * (s + 1) * (i - 2 * k - s) : ℕ) : F)

def cK (ρ : F) (_s : ℕ) : F := -ρ

def detK (θA θB ρ : F) (i j k : ℕ) : F :=
  cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)

def GK (θA θB ρ : F) (i j k s s' : ℕ) : F :=
  usmaniEntry (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1) s s' / detK θA θB ρ i j k

end Rhone.LinearAlgebra.BooleanLatticeInverse

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Matrix Tridiag RecombinationExpansion

variable {F : Type*} [Field F] {i : ℕ}

def phiK (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) (k s : ℕ) : Finset (Fin i) → F :=
  ∑ s' ∈ range (sig i j k + 1), GK θA θB ρ i j k s s' • proj k (k + s') (lev (k + s') R)

def blockSol (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) : Finset (Fin i) → F := fun S =>
  (∑ k ∈ range (min S.card (i - S.card) + 1),
    (D ^ (S.card - k)) (phiK θA θB ρ j R k (S.card - k))) S

end Rhone.LinearAlgebra.BooleanLatticeInverse

clear_aux_proof_cache

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Recursion

variable {KA : ℕ} {F : Type*} [Field F]

def pull {n : ℕ} (x : Fin (n + 1)) (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun y => x.succAbove y ∈ S

def kapA (πA : Fin KA → F) (p p' : Fin KA) : F :=
  (if p = p' then πA p else 0) - πA p * πA p'

def kapB (πB : Fin 2 → F) : F := πB 0 * πB 1

def gamB (πB : Fin 2 → F) : F := πB 1 - πB 0

abbrev Tab (KA : ℕ) (F : Type*) : Type _ :=
  (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F

section Source

variable (πA : Fin KA → F) (πB : Fin 2 → F) (P : Tab KA F)

def aTerm : (n : ℕ) → (Fin n → Fin KA) → Fin KA → ℕ → Finset (Fin n) → Fin n → F
  | 0, _, _, _, _, _ => 0
  | n + 1, lab, p', j, S, z =>
    kapA πA (lab z) p' * P n (lab ∘ z.succAbove) j (pull z S)
      + ((if lab z = p' then 1 else 0) - πA p') * P (n + 1) lab j S
      - πA (lab z) * P (n + 1) (Function.update lab z p') j S

def pairSrc : (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F
  | 0, _, _, _ => 0
  | n + 1, lab, j, S =>
    ∑ x' : Fin (n + 1), ∑ z : Fin n,
      if x' ∈ S then
        if z ∈ pull x' S then
          kapB πB * aTerm πA P n (lab ∘ x'.succAbove) (lab x') (j - 2) ((pull x' S).erase z) z
            + gamB πB * aTerm πA P n (lab ∘ x'.succAbove) (lab x') (j - 1) (pull x' S) z
        else 0
      else
        (if z ∈ pull x' S then 2 else 1)
          * aTerm πA P n (lab ∘ x'.succAbove) (lab x') j (pull x' S) z

def srcKB2 (n : ℕ) (lab : Fin n → Fin KA) (j : ℕ) (S : Finset (Fin n)) : F :=
  pairSrc πA πB P n lab j S
    + (((j - S.card) * (j - S.card - 1) : ℕ) : F)
      * (kapB πB * P n lab (j - 2) S + gamB πB * P n lab (j - 1) S)
    + 2 * ((j - S.card : ℕ) : F)
      * ∑ x ∈ S, (kapB πB * P n lab (j - 2) (S.erase x) + gamB πB * P n lab (j - 1) S)

end Source

def PhiTab (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) : ℕ → Tab KA F
  | 0, _, _, _, _ => 1
  | f + 1, n, lab, j, S =>
    if n + j = 0 then 1
    else blockSol θA θB ρ j (srcKB2 πA πB (PhiTab θA θB ρ πA πB f) n lab j) S

def PhiX (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) : Tab KA F :=
  fun n lab j S => PhiTab θA θB ρ πA πB (n + j) n lab j S

inductive Slot (KA : ℕ) : Type

  | freeA (p : Fin KA)

  | freeB (b : Fin 2)

  | pair (p : Fin KA) (b : Fin 2)

def slots (ξ : Config KA 2) : List (Slot KA) :=
  ((List.finRange KA).flatMap fun p => List.replicate (ξ.a p) (Slot.freeA p))
    ++ ((List.finRange 2).flatMap fun b => List.replicate (ξ.b b) (Slot.freeB b))
    ++ ((List.finRange KA).flatMap fun p => (List.finRange 2).flatMap fun b =>
      List.replicate (ξ.c p b) (Slot.pair p b))

def sgnB (b : Fin 2) : F := if b = 0 then 1 else -1

def asm (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) :
    List (Slot KA) → (n : ℕ) → (Fin n → Fin KA) → ℕ → Finset (Fin n) → F
  | [], n, lab, j, S => PhiX θA θB ρ πA πB n lab j S
  | Slot.freeA p :: r, n, lab, j, S =>
    πA p * asm θA θB ρ πA πB r n lab j S
      + asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) j
        (S.map (Fin.succEmb n))
  | Slot.freeB b :: r, n, lab, j, S =>
    πB b * asm θA θB ρ πA πB r n lab j S + sgnB b * asm θA θB ρ πA πB r n lab (j + 1) S
  | Slot.pair p b :: r, n, lab, j, S =>
    πA p * πB b * asm θA θB ρ πA πB r n lab j S
      + πB b * asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) j
        (S.map (Fin.succEmb n))
      + πA p * sgnB b * asm θA θB ρ πA πB r n lab (j + 1) S
      + sgnB b * asm θA θB ρ πA πB r (n + 1) (Fin.cons p lab : Fin (n + 1) → Fin KA) (j + 1)
        (insert 0 (S.map (Fin.succEmb n)))

def qExplicitKB2 (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin 2 → F) (ξ : Config KA 2) : F :=
  asm θA θB ρ πA πB (slots ξ) 0 Fin.elim0 0 ∅

end Rhone.LinearAlgebra.BooleanLatticeInverse

namespace Rhone.Palomar.ExplicitFormula

open Finset LinearAlgebra.Recursion Probability.ExplicitFormula LinearAlgebra.AlleleLumping

theorem q_eq_qExplicit {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config 2 2) :
    q ξ = qExplicit θA θB ρ πA πB ξ := by
  sorry

theorem qExplicit_isSolution {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    IsSolution θA θB ρ πA πB (qExplicit θA θB ρ πA πB) := by
  sorry

theorem lump_isSolution {KA KB KA' KB' : ℕ} {F : Type*} [Field F] [CharZero F]
    {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F} {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q)
    (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB')
    (S : Config KA' KB' → Finset (Config KA KB))
    (hS : ∀ η ξ, ξ ∈ S η ↔ push fA fB ξ = η) :
    IsSolution θA θB ρ (pushPi fA πA) (pushPi fB πB)
      (fun η => (mult η : F)⁻¹ * ∑ ξ ∈ S η, (mult ξ : F) * q ξ) := by
  sorry

theorem lumping_eq_qExplicit {KA KB : ℕ} {F : Type*} [Field F] [CharZero F]
    [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F} {q : Config KA KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hq : IsSolution θA θB ρ πA πB q)
    (fA : Fin KA → Fin 2) (fB : Fin KB → Fin 2) (η : Config 2 2)
    (S : Finset (Config KA KB)) (hS : ∀ ξ, ξ ∈ S ↔ push fA fB ξ = η) :
    (mult η : F) * qExplicit θA θB ρ (pushPi fA πA) (pushPi fB πB) η
      = ∑ ξ ∈ S, (mult ξ : F) * q ξ := by
  sorry

section KB2

open LinearAlgebra.BooleanLatticeInverse

theorem q_eq_qExplicitKB2 {KA : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F} {q : Config KA 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA 2) :
    q ξ = qExplicitKB2 θA θB ρ πA πB ξ := by
  sorry

end KB2

end Rhone.Palomar.ExplicitFormula
