module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Fin.VecNotation

set_option maxSynthPendingDepth 3

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset

variable {KA KB : ℕ}

def incf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i + 1)

def decf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i - 1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem exists_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  sorry

noncomputable def q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : Config KA KB → F :=
  Classical.choose (exists_isSolution (πA := πA) (πB := πB) hθA hθB hρ)

end Rhone.LinearAlgebra.Recursion

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

section Rising

variable {F : Type*} [Field F]

def rising (x : F) (k : ℕ) : F := ∏ r ∈ Finset.range k, (x + (r : ℕ))

end Rising

section QOne

variable {K : ℕ} {F : Type*} [Field F] {θ : F} {π : Fin K → F}

def qOne (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F :=
  (∏ i, rising (θ * π i) (m i)) / rising θ (∑ i, m i)

end QOne

end Rhone.LinearAlgebra.Recursion

namespace Rhone.MarkovChain.ClosedForms

open Finset Matrix LinearAlgebra.Recursion Config

section Ring

variable {R : Type*} [CommRing R]

def Eblock (θA θB ρ : R) : R :=
  (θA + θB + 2) * ρ ^ 2 + (θA + θB + 2) * (3 * (θA + θB) + 13) * ρ
    + 2 * (θA + θB + 1) * (θA + θB + 3) * (θA + θB + 6)

def wvec (θA θB ρ : R) : Fin 3 → R :=
  ![16, 4 * (θA + θB + 6),
    4 * (θA + θB + 3) * (θA + θB + 6) + 2 * ρ * (θA + θB + 2)]

end Ring

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F}

def wn (θA θB ρ : F) : ℕ → F
  | 0 => 16
  | 1 => 4 * (θA + θB + 6)
  | 2 => 4 * (θA + θB + 3) * (θA + θB + 6) + 2 * ρ * (θA + θB + 2)
  | _ + 3 => 0

def gf (θA θB ρ : F) (t : ℕ) : F := wn θA θB ρ t / (2 * Eblock θA θB ρ)

end Rhone.MarkovChain.ClosedForms

namespace Rhone.MarkovChain.ClosedForms

open Finset LinearAlgebra.Recursion

variable {K : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {π : Fin K → F}

def Gval (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F :=
  qOne θ π m - ∑ i, ((Nat.choose (m i) 2 : ℕ) : F) * qOne θ π (decf m i)

end Rhone.MarkovChain.ClosedForms

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def qHat (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (ξ : Config KA KB) : F :=
  qOne θA πA ξ.mA * qOne θB πB ξ.mB

end Rhone.Probability.Denominator

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset

variable {n : ℕ}

abbrev Lin (n : ℕ) : Type := Finset (Fin n) × Finset (Fin n)

def carA (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.1.Nonempty

def carB (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.2.Nonempty

def carC (L : Finset (Lin n)) : Finset (Lin n) :=
  L.filter fun p => p.1.Nonempty ∧ p.2.Nonempty

def na (L : Finset (Lin n)) : ℕ := (carA L).card

def nb (L : Finset (Lin n)) : ℕ := (carB L).card

def tt (L : Finset (Lin n)) : ℕ := (carC L).card

def coalL (L : Finset (Lin n)) (p q : Lin n) : Finset (Lin n) :=
  insert (p.1 ∪ q.1, p.2 ∪ q.2) ((L.erase p).erase q)

def mutAL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  if p.2 = ∅ then L.erase p else insert (∅, p.2) (L.erase p)

def mutBL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  if p.1 = ∅ then L.erase p else insert (p.1, ∅) (L.erase p)

def recL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  insert (p.1, ∅) (insert (∅, p.2) (L.erase p))

end Rhone.Coalescent.TwoLocusGenealogy

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {F : Type*} [Field F]

variable (σA σB)

def matchA (πA : Fin KA → F) (S : Finset (Fin n)) : F :=
  ∑ i, if ∀ k ∈ S, σA k = i then πA i else 0

def matchB (πB : Fin KB → F) (T : Finset (Fin n)) : F :=
  ∑ j, if ∀ k ∈ T, σB k = j then πB j else 0

variable {σA σB}

variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (σA σB)

def dtot (L : Finset (Lin n)) : F :=
  ((L.card * (L.card - 1) : ℕ) : F) + θA * ((na L : ℕ) : F) + θB * ((nb L : ℕ) : F)
    + ρ * ((tt L : ℕ) : F)

end Rhone.Coalescent.TwoLocusGenealogy

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def fullState (n : ℕ) : Finset (Lin n) := Finset.univ.image fun k => ({k}, {k})

def cSample (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, fun i j => (Finset.univ.filter fun k => σA k = i ∧ σB k = j).card⟩

end Rhone.Coalescent.TwoLocusGenealogy

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy

variable {n : ℕ}

abbrev Blocks (n : ℕ) : Type := Finset (Finset (Fin n))

abbrev PSt (n : ℕ) : Type := Finset (Lin n) × Blocks n × Blocks n

def coalP (s : PSt n) (p q : Lin n) : PSt n := (coalL s.1 p q, s.2.1, s.2.2)

def mutAP (s : PSt n) (p : Lin n) : PSt n := (mutAL s.1 p, insert p.1 s.2.1, s.2.2)

def mutBP (s : PSt n) (p : Lin n) : PSt n := (mutBL s.1 p, s.2.1, insert p.2 s.2.2)

def recP (s : PSt n) (p : Lin n) : PSt n := (recL s.1 p, s.2.1, s.2.2)

structure IsPartOf (S : Finset (Fin n)) (ζ : Blocks n) : Prop where

  ne : ∀ β ∈ ζ, β.Nonempty

  pd : ∀ β ∈ ζ, ∀ β' ∈ ζ, β ≠ β' → Disjoint β β'

  cover : ζ.biUnion id = S

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy

variable {n : ℕ} {θA θB ρ : ℝ}

def stepP (θA θB ρ : ℝ) (g : PSt n → ℝ) (s : PSt n) : ℝ :=
  (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g (coalP s p q))
    + θA * (∑ p ∈ carA s.1, g (mutAP s p))
    + θB * (∑ p ∈ carB s.1, g (mutBP s p))
    + ρ * (∑ p ∈ carC s.1, g (recP s p))

def hitAt (ζA ζB : Blocks n) (s : PSt n) : ℝ := if s.2.1 = ζA ∧ s.2.2 = ζB then 1 else 0

noncomputable def hitNP (ζA ζB : Blocks n) (θA θB ρ : ℝ) : ℕ → PSt n → ℝ
  | 0, s => if s.1 = ∅ then hitAt ζA ζB s else 0
  | N + 1, s =>
      if s.1 = ∅ then hitAt ζA ζB s
      else stepP θA θB ρ (hitNP ζA ζB θA θB ρ N) s / dtot θA θB ρ s.1

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

noncomputable def wA (σA : Fin n → Fin KA) (πA : Fin KA → ℝ) (ζ : Blocks n) : ℝ :=
  ∏ β ∈ ζ, matchA σA πA β

noncomputable def wB (σB : Fin n → Fin KB) (πB : Fin KB → ℝ) (ζ : Blocks n) : ℝ :=
  ∏ γ ∈ ζ, matchB σB πB γ

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset Filter Topology TwoLocusGenealogy

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB} {ζA ζB : Blocks n}

noncomputable def PPst (θA θB ρ : ℝ) (ζA ζB : Blocks n) (s : PSt n) : ℝ :=
  ⨆ N, hitNP ζA ζB θA θB ρ N s

def initP (n : ℕ) : PSt n := (fullState n, ∅, ∅)

noncomputable def esfKernel (θA θB ρ : ℝ) (ζA ζB : Blocks n) : ℝ :=
  PPst θA θB ρ ζA ζB (initP n)

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset Coalescent.TwoLocusGenealogy

variable {n : ℕ}

instance (S : Finset (Fin n)) (ζ : Coalescent.EsfPair.Blocks n) : Decidable
    (Coalescent.EsfPair.IsPartOf S ζ) :=
  decidable_of_iff ((∀ β ∈ ζ, β.Nonempty) ∧ (∀ β ∈ ζ, ∀ β' ∈ ζ, β ≠ β' → Disjoint β β')
      ∧ ζ.biUnion id = S)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.ne, h.pd, h.cover⟩⟩

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n : ℕ} {θA θB ρ : ℝ}

noncomputable def esfPart (n : ℕ) (θ : ℝ) (ζ : Blocks n) : ℝ :=
  if IsPartOf (Finset.univ : Finset (Fin n)) ζ then
    (θ ^ ζ.card * ∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ)) / rising θ n
  else 0

noncomputable def margB (θA θB ρ : ℝ) (ζB : Blocks n) : ℝ :=
  ∑ ζA : Blocks n, esfKernel θA θB ρ ζA ζB

end Rhone.Coalescent.EsfPair

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n : ℕ} {θA θB ρ : ℝ}

def meet (ζA ζB : Blocks n) : Blocks n := (((ζA ×ˢ ζB).image fun x => x.1 ∩ x.2)).erase ∅

noncomputable def meetLaw (n : ℕ) (θA θB ρ : ℝ) (ζ : Blocks n) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset (Blocks n × Blocks n)).filter fun x => meet x.1 x.2 = ζ,
    esfKernel θA θB ρ x.1 x.2

end Rhone.Coalescent.EsfPair

namespace Rhone.Palomar.PartitionPair

open Filter Topology Coalescent Rhone.LinearAlgebra MarkovChain Probability LinearAlgebra.Recursion
  Coalescent.TwoLocusGenealogy Coalescent.EsfPair Probability.Denominator MarkovChain.ClosedForms

theorem esf_pair_decomposition {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
      = ∑ ζA : Blocks n, ∑ ζB : Blocks n,
          esfKernel θA θB ρ ζA ζB * wA σA πA ζA * wB σB πB ζB := by
  sorry

theorem margA_eq_esfPart {n : ℕ} {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ζA : Blocks n) :
    (∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB) = esfPart n θA ζA := by
  sorry

theorem margB_eq_esfPart {n : ℕ} {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ζB : Blocks n) :
    margB θA θB ρ ζB = esfPart n θB ζB := by
  sorry

theorem tendsto_esfKernel_prod {n : ℕ} {θA θB : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (ζA ζB : Blocks n) :
    Tendsto (fun ρ : ℝ => esfKernel θA θB ρ ζA ζB) atTop
      (𝓝 (esfPart n θA ζA * esfPart n θB ζB)) := by
  sorry

theorem meetLaw_rho_zero_eq_esfPart {n : ℕ} {θA θB : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (ζ : Blocks n) :
    meetLaw n θA θB 0 ζ = esfPart n (θA + θB) ζ := by
  sorry

theorem product_family_iff {KA KB : ℕ} (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) :
    (∀ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
        (∀ i, 0 < πA i) → (∑ i, πA i = 1) → (∀ j, 0 < πB j) → (∑ j, πB j = 1) →
        ∀ (ρ : ℝ) (hρ : 0 ≤ ρ),
          Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ = qHat θA θB πA πB ξ)
      ↔ (ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) := by
  sorry

theorem block22_closed_form {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q ξ = qHat θA θB πA πB ξ
      + Gval θA πA ξ.mA * Gval θB πB ξ.mB * gf θA θB ρ ξ.t := by
  sorry

end Rhone.Palomar.PartitionPair
