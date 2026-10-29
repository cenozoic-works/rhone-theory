module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

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

section Exist

open Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem exists_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  sorry

noncomputable def q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : Config KA KB → F :=
  Classical.choose (exists_isSolution (πA := πA) (πB := πB) hθA hθB hρ)

end Exist

section OneLocus

open Config

section Rising

variable {F : Type*} [Field F]

def rising (x : F) (k : ℕ) : F := ∏ r ∈ Finset.range k, (x + (r : ℕ))

end Rising

section QOne

variable {K : ℕ} {F : Type*} [Field F] {θ : F} {π : Fin K → F}

def qOne (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F :=
  (∏ i, rising (θ * π i) (m i)) / rising θ (∑ i, m i)

end QOne

end OneLocus

end Rhone.LinearAlgebra.Recursion

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

section PIM

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def pimMat (π : Fin KA → F) : Fin KA → Fin KA → F := fun _ i => π i

end PIM

section OneLocusG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {ν : ι → F} {P : ι → ι → F}

structure IsSolutionOneG (θ : F) (ν : ι → F) (P : ι → ι → F) (q : (ι → ℕ) → F) : Prop where

  empty : q (fun _ => 0) = 1

  bdry : ∀ x, q (incf (fun _ => 0) x) = ν x

  recursion : ∀ m : ι → ℕ, 2 ≤ ∑ x, m x →
    ((((∑ x, m x) * ((∑ x, m x) - 1) : ℕ) : F) + θ * ((∑ x, m x : ℕ) : F)) * q m
      = (∑ x, ((m x * (m x - 1) : ℕ) : F) * q (decf m x))
        + θ * ∑ x, ∑ y, P y x * ((m x : ℕ) : F) * q (incf (decf m x) y)

end OneLocusG

section RhoZero

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

def full (m : Fin KA × Fin KB → ℕ) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, fun i j => m (i, j)⟩

def prodMat (θA θB : F) (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F) :
    (Fin KA × Fin KB) → (Fin KA × Fin KB) → F := fun y x =>
  (θA * (if y.2 = x.2 then PA y.1 x.1 else 0) + θB * (if y.1 = x.1 then PB y.2 x.2 else 0))
    / (θA + θB)

def prodNu (νA : Fin KA → F) (νB : Fin KB → F) : Fin KA × Fin KB → F :=
  fun x => νA x.1 * νB x.2

end RhoZero

end Rhone.MarkovChain.GeneralMutation

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset

section State

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

end State

section Step

variable {n : ℕ}
variable {F : Type*} [Field F]
variable (θA θB ρ : F)

def dtot (L : Finset (Lin n)) : F :=
  ((L.card * (L.card - 1) : ℕ) : F) + θA * ((na L : ℕ) : F) + θB * ((nb L : ℕ) : F)
    + ρ * ((tt L : ℕ) : F)

end Step

section Prob

open LinearAlgebra.Recursion

variable {n KA KB : ℕ}

def fullState (n : ℕ) : Finset (Lin n) := Finset.univ.image fun k => ({k}, {k})

def cSample (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, fun i j => (Finset.univ.filter fun k => σA k = i ∧ σB k = j).card⟩

end Prob

section Kernel

variable {n : ℕ}

noncomputable def rateTot (θA θB ρ : ℝ) (L : Finset (Lin n)) : ℝ :=
  ((L.card * (L.card - 1) : ℕ) : ℝ) / 2 + θA / 2 * ((na L : ℕ) : ℝ)
    + θB / 2 * ((nb L : ℕ) : ℝ) + ρ / 2 * ((tt L : ℕ) : ℝ)

end Kernel

end Rhone.Coalescent.TwoLocusGenealogy

namespace Rhone.Coalescent.Rational

open Filter Topology Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def qAt (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ρ : ℝ) : Config KA KB → ℝ :=
  if h : 0 ≤ ρ then LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB h else fun _ => 0

end Rhone.Coalescent.Rational

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory

section Types

variable {n KA KB : ℕ}

abbrev TSt (n KA KB : ℕ) : Type :=
  Finset (Lin n) × (Fin n → Option (Fin KA)) × (Fin n → Option (Fin KB))

def setT {K : ℕ} (τ : Fin n → Option (Fin K)) (S : Finset (Fin n)) (i : Fin K) :
    Fin n → Option (Fin K) := fun k => if k ∈ S then some i else τ k

def FitsT {K : ℕ} (σ : Fin n → Fin K) (τ : Fin n → Option (Fin K)) : Prop :=
  ∀ k i, τ k = some i → σ k = i

def Fits (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (s : TSt n KA KB) : Prop :=
  FitsT σA s.2.1 ∧ FitsT σB s.2.2

end Types

section Step

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def stepT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (g : TSt n KA KB → ℝ)
    (s : TSt n KA KB) : ℝ :=
  (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g (coalL s.1 p q, s.2.1, s.2.2))
    + θA * (∑ p ∈ carA s.1, ∑ i, πA i * g (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2))
    + θB * (∑ p ∈ carB s.1, ∑ j, πB j * g (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j))
    + ρ * (∑ p ∈ carC s.1, g (recL s.1 p, s.2.1, s.2.2))

noncomputable def transT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (s t : TSt n KA KB) : ℝ :=
  if 0 < dtot θA θB ρ s.1 then
    stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s / dtot θA θB ρ s.1
  else if t = s then 1 else 0

end Step

section Link

variable {n KA KB : ℕ}

def noneT (n K : ℕ) : Fin n → Option (Fin K) := fun _ => none

def initT (n KA KB : ℕ) : TSt n KA KB := (fullState n, noneT n KA, noneT n KB)

end Link

section KernelT

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

structure TS (n KA KB : ℕ) : Type where

  st : TSt n KA KB
  deriving DecidableEq

namespace TS

def equivTSt : TS n KA KB ≃ TSt n KA KB where
  toFun := TS.st
  invFun := TS.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : MeasurableSpace (TS n KA KB) := ⊤
instance : Fintype (TS n KA KB) := Fintype.ofEquiv _ (equivTSt (n := n) (KA := KA) (KB := KB)).symm
instance : Inhabited (TS n KA KB) := ⟨⟨((∅ : Finset (Lin n)), noneT n KA, noneT n KB)⟩⟩
instance : Nonempty (TS n KA KB) := ⟨default⟩
instance : DiscreteMeasurableSpace (TS n KA KB) := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass (TS n KA KB) := ⟨fun _ => trivial⟩

end TS

noncomputable def transS (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (s t : TS n KA KB) : ℝ := transT θA θB ρ πA πB s.st t.st

theorem transS_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (s t : TS n KA KB) : 0 ≤ transS θA θB ρ πA πB s t := by
  sorry

theorem sum_transS (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (s : TS n KA KB) :
    (∑ t : TS n KA KB, transS θA θB ρ πA πB s t) = 1 := by
  sorry

structure Adm (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) : Prop where

  thA : 0 ≤ θA

  thB : 0 ≤ θB

  rho : 0 ≤ ρ

  piA : ∀ i, 0 ≤ πA i

  piB : ∀ j, 0 ≤ πB j

  sumA : ∑ i, πA i = 1

  sumB : ∑ j, πB j = 1

noncomputable def onePMFT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (s : TS n KA KB) : PMF (TS n KA KB) :=
  PMF.ofFintype (fun t : TS n KA KB => ENNReal.ofReal (transS θA θB ρ πA πB s t)) (by
    have hnn : ∀ t ∈ (Finset.univ : Finset (TS n KA KB)), 0 ≤ transS θA θB ρ πA πB s t :=
      fun t _ => transS_nonneg h.thA h.thB h.rho h.piA h.piB s t
    rw [(ENNReal.ofReal_sum_of_nonneg hnn).symm, sum_transS h.sumA h.sumB s,
      ENNReal.ofReal_one])

noncomputable def argKernelT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) : Kernel (TS n KA KB) (TS n KA KB) where
  toFun s := (onePMFT θA θB ρ πA πB h s).toMeasure
  measurable' := Measurable.of_discrete

variable (h : Adm θA θB ρ πA πB)

theorem argKernelT_apply (s : TS n KA KB) :
    argKernelT θA θB ρ πA πB h s
      = (onePMFT θA θB ρ πA πB h s).toMeasure := rfl

instance isMarkovKernel_argKernelT :
    IsMarkovKernel (argKernelT (n := n) θA θB ρ πA πB h) :=
  ⟨fun s => by rw [argKernelT_apply]; infer_instance⟩

noncomputable def argSeqT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (m : ℕ) :
    Kernel ((_i : Finset.Iic m) → TS n KA KB) (TS n KA KB) :=
  (argKernelT θA θB ρ πA πB h).comap
    (fun x => x ⟨m, Finset.mem_Iic.2 le_rfl⟩) Measurable.of_discrete

instance isMarkovKernel_argSeqT (m : ℕ) :
    IsMarkovKernel (argSeqT (n := n) θA θB ρ πA πB h m) := by
  rw [argSeqT]
  infer_instance

noncomputable def argTrajT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    Measure ((_ : ℕ) → TS n KA KB) :=
  Kernel.traj (X := fun _ => TS n KA KB)
    (argSeqT θA θB ρ πA πB h) 0 (fun _ => s)

end KernelT

section Event

variable {n KA KB : ℕ}

def TFin (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) : Set (TS n KA KB) :=
  {t | t.st.1 = ∅ ∧ Fits σA σB t.st}

end Event

end Rhone.Coalescent.TypedAncestralChain

namespace Rhone.Coalescent.BranchLengthMoments

open Finset TwoLocusGenealogy TypedAncestralChain LinearAlgebra.Recursion
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def occAll (g : TS n KA KB → ℝ) (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (g (ω k))

noncomputable def rateTotS (θA θB ρ : ℝ) (s : TS n KA KB) : ℝ := rateTot θA θB ρ s.st.1

def rA (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  ((t.st.1.filter fun p => p.1 ∈ F).card : ℝ)

def cladeFam (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => S.Nonempty ∧ S ≠ Finset.univ

noncomputable def holdA (θA θB ρ : ℝ) (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  rA F t / rateTotS θA θB ρ t

noncomputable def branchLen (θA θB ρ : ℝ) (F : Finset (Finset (Fin n)))
    (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  occAll (holdA θA θB ρ F) ω

end Rhone.Coalescent.BranchLengthMoments

namespace Rhone.Palomar.SamplingRecursion

open Filter Topology MeasureTheory
open Coalescent Rhone.LinearAlgebra MarkovChain LinearAlgebra.Recursion Coalescent.TwoLocusGenealogy
  Coalescent.TypedAncestralChain Coalescent.BranchLengthMoments Coalescent.Rational
  MarkovChain.GeneralMutation

theorem exists_isSolution {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  sorry

theorem isSolution_unique {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolution θA θB ρ πA πB q₁)
    (h₂ : IsSolution θA θB ρ πA πB q₂) : q₁ = q₂ := by
  sorry

theorem measure_hit_ever_initT {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
    (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    argTrajT θA θB ρ πA πB h ⟨initT n KA KB⟩ {ω | ∃ k, ω k ∈ TFin σA σB}
      = ENNReal.ofReal (Recursion.q (πA := πA) (πB := πB) hθA hθB h.rho
          (cSample σA σB)) := by
  sorry

theorem sum_q_cSample {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hsA : ∑ i, πA i = 1)
    (hsB : ∑ j, πB j = 1) (n : ℕ) :
    (∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
      Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)) = 1 := by
  sorry

theorem tendsto_q_qHat {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    Tendsto (fun ρ => qAt hθA hθB πA πB ρ ξ) atTop
      (𝓝 (qOne θA πA ξ.mA * qOne θB πB ξ.mB)) := by
  sorry

theorem isSolutionOneG_q_rho_zero {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB : F} {νA : Fin KA → F} {νB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB)
    (hπA : ∑ i, νA i = 1) (hπB : ∑ j, νB j = 1) :
    IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB (pimMat νA) (pimMat νB))
      (fun m => Recursion.q (πA := νA) (πB := νB) hθA hθB le_rfl (full m)) := by
  sorry

theorem expected_total_length {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      = ENNReal.ofReal (2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) := by
  sorry

end Rhone.Palomar.SamplingRecursion
