module

public import Rhone.Coalescent.EsfPair.Decomp
public import Rhone.Coalescent.EsfPair.Final
public import Rhone.Coalescent.PartitionCarryingChain.Final
public import Rhone.Coalescent.InfiniteAllelesLimit.Limit
public import Rhone.Coalescent.Converse.ProductFamilyConverse
public import Rhone.MarkovChain.BilinearForm.Block22

@[expose] public section

namespace Rhone.Palomar.PartitionPair

open Filter Topology Rhone.Algebra Analysis Coalescent Rhone.LinearAlgebra MarkovChain Probability
  LinearAlgebra.Recursion Coalescent.TwoLocusGenealogy Coalescent.EsfPair Probability.Denominator
  MarkovChain.ClosedForms

theorem esf_pair_decomposition {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
      = ∑ ζA : Blocks n, ∑ ζB : Blocks n,
          esfKernel θA θB ρ ζA ζB * wA σA πA ζA * wB σB πB ζB :=
  Rhone.Coalescent.EsfPair.esf_pair_decomposition hθA hθB hρ hπA hsA hπB hsB σA σB

theorem margA_eq_esfPart {n : ℕ} {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ζA : Blocks n) :
    (∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB) = esfPart n θA ζA :=
  Rhone.Coalescent.EsfPair.margA_eq_esfPart hθA hθB hρ ζA

theorem margB_eq_esfPart {n : ℕ} {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ζB : Blocks n) :
    margB θA θB ρ ζB = esfPart n θB ζB :=
  Rhone.Coalescent.EsfPair.margB_eq_esfPart hθA hθB hρ ζB

theorem tendsto_esfKernel_prod {n : ℕ} {θA θB : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (ζA ζB : Blocks n) :
    Tendsto (fun ρ : ℝ => esfKernel θA θB ρ ζA ζB) atTop
      (𝓝 (esfPart n θA ζA * esfPart n θB ζB)) :=
  Rhone.Coalescent.InfiniteAllelesLimit.tendsto_esfKernel_prod hθA hθB ζA ζB

theorem meetLaw_rho_zero_eq_esfPart {n : ℕ} {θA θB : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (ζ : Blocks n) :
    meetLaw n θA θB 0 ζ = esfPart n (θA + θB) ζ :=
  Rhone.Coalescent.PartitionCarryingChain.meetLaw_rho_zero_eq_esfPart hθA hθB ζ

theorem product_family_iff {KA KB : ℕ} (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) :
    (∀ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
        (∀ i, 0 < πA i) → (∑ i, πA i = 1) → (∀ j, 0 < πB j) → (∑ j, πB j = 1) →
        ∀ (ρ : ℝ) (hρ : 0 ≤ ρ),
          Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ = qHat θA θB πA πB ξ)
      ↔ (ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) :=
  Rhone.Coalescent.Converse.product_family_iff hKA hKB ξ

theorem block22_closed_form {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q ξ = qHat θA θB πA πB ξ
      + Gval θA πA ξ.mA * Gval θB πB ξ.mB * gf θA θB ρ ξ.t :=
  Rhone.MarkovChain.BilinearForm.block22_closed_form' hθA hθB hρ hq hA hB

end Rhone.Palomar.PartitionPair
