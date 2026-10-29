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

variable {KA KB : ℕ} {SA SB : Type*}

section ADom

variable [DecidableEq SA]

def domA (M : Finset (SA × SB)) : Finset SA := M.image Prod.fst

variable [Fintype SA]

def freeA (M : Finset (SA × SB)) : Finset SA := univ \ domA M

end ADom

section BDom

variable [DecidableEq SB]

def domB (M : Finset (SA × SB)) : Finset SB := M.image Prod.snd

variable [Fintype SB]

def freeB (M : Finset (SA × SB)) : Finset SB := univ \ domB M

end BDom

section Xi

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def xi (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB) : Config KA KB where
  a i := ((freeA M).filter fun u => α u = i).card
  b j := ((freeB M).filter fun v => β v = j).card
  c i j := (M.filter fun p => α p.1 = i ∧ β p.2 = j).card

end Xi

end Rhone.Probability.Multilinear

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [CommRing F] {SA SB : Type*}

section Q

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def Q (q : Config KA KB → F) (M : Finset (SA × SB))
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) : F :=
  ∑ α : SA → Fin KA, ∑ β : SB → Fin KB,
    (∏ u, s u (α u)) * (∏ v, w v (β v)) * q (xi M α β)

end Q

end Rhone.Probability.Multilinear

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

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

def canM (i j t : ℕ) : Finset (Fin i × Fin j) :=
  (univ : Finset (Fin i × Fin j)).filter fun p => (p.1 : ℕ) = (p.2 : ℕ) ∧ (p.1 : ℕ) < t

variable {F : Type*} [Field F] {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

noncomputable def Phi (q : Config 2 2 → F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  Q q (canM i j t) (fun _ => fvec πA) (fun _ => fvec πB)

end Rhone.Probability.Multilinear

namespace Rhone.LinearAlgebra.SlotDeletion

open Finset

variable {R : Type*} [CommRing R]

def poch (θ : R) (n : ℕ) : R := ∏ k ∈ Finset.Ico 1 n, (θ + (k : R))

def Erect (a b r : R) (i j : ℕ) : R :=
  ∏ p ∈ Finset.Ico 2 (i + 1), ∏ s ∈ Finset.Ico 2 (j + 1), Tridiag.E R p s a b r

def Dfull (a b r : R) (i j : ℕ) : R := poch a i * poch b j * Erect a b r i j

end Rhone.LinearAlgebra.SlotDeletion

clear_aux_proof_cache

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Multilinear

section R

variable {F : Type*} [Field F]

noncomputable def phiRecursionSource (q : Config 2 2 → F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  kap πA * ((((i - t) * (i - t - 1) : ℕ) : F) * Phi q πA πB (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : F) * Phi q πA πB (i - 2) j (t - 1))
    + gam πA * (((i - t) * (i + t - 1) : ℕ) : F) * Phi q πA πB (i - 1) j t
    + kap πB * ((((j - t) * (j - t - 1) : ℕ) : F) * Phi q πA πB i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : F) * Phi q πA πB i (j - 2) (t - 1))
    + gam πB * (((j - t) * (j + t - 1) : ℕ) : F) * Phi q πA πB i (j - 1) t
    + ((t * (t - 1) : ℕ) : F) * (kap πA * kap πB * Phi q πA πB (i - 2) (j - 2) (t - 2)
      + kap πA * gam πB * Phi q πA πB (i - 2) (j - 1) (t - 2)
      + gam πA * kap πB * Phi q πA πB (i - 1) (j - 2) (t - 2)
      + gam πA * gam πB * Phi q πA πB (i - 1) (j - 1) (t - 1))

end R

end Rhone.Probability.SlotDeletion

namespace Rhone.Algebra.Denominator

variable {F : Type*} [Field F]

def Clears (A : Subring F) (x d : F) : Prop := d ∈ A ∧ d * x ∈ A

def DvdIn (A : Subring F) (e x : F) : Prop := ∃ k ∈ A, x = e * k

structure IsRedDenom (A : Subring F) (x D : F) : Prop where

  clears : Clears A x D

  min : ∀ d, Clears A x d → DvdIn A D d

end Rhone.Algebra.Denominator

namespace Rhone.Palomar.DenominatorLaw

open Polynomial Rhone.Algebra Rhone.LinearAlgebra Probability LinearAlgebra.Tridiag
open LinearAlgebra.Recursion
  Probability.Multilinear LinearAlgebra.SlotDeletion Probability.SlotDeletion Algebra.Denominator
open scoped Matrix

theorem T_mulVec_Phi_eq_phiRecursionSource {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j : ℕ) :
    Tridiag.T F i j θA θB ρ *ᵥ (fun t : Fin (min i j + 1) => Phi q πA πB i j (t : ℕ))
      = fun t : Fin (min i j + 1) => phiRecursionSource q πA πB i j (t : ℕ) := by
  sorry

theorem Dfull_mul_q_mem {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (ξ : Config 2 2) :
    Dfull θA θB ρ ξ.nA ξ.nB * q ξ ∈ A := by
  sorry

theorem dvdIn_E_of_clears {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB)
    (hH : IsRedDenom A (Phi q πA πB ξ.nA ξ.nB ξ.t) (Dfull θA θB ρ ξ.nA ξ.nB))
    {d : F} (hd : Clears A (q ξ) d) :
    DvdIn A (Tridiag.E F ξ.nA ξ.nB θA θB ρ) d := by
  sorry

theorem natDegree_E {F : Type*} [CommRing F] (i j : ℕ) (a b : F)
    (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j := by
  sorry

theorem E_pos {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F] {i j : ℕ}
    {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    0 < E F i j θA θB ρ := by
  sorry

theorem unbounded_irreducible_E_mm_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m X 0 (C RatFunc.X) ∧
      D < G.natDegree := by
  sorry

theorem unbounded_irreducible_E_mm_recombination_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m (C RatFunc.X) 0 X ∧
      D < G.natDegree := by
  sorry

end Rhone.Palomar.DenominatorLaw
