module

public import Rhone.LinearAlgebra.Recursion.Exist
public import Rhone.Coalescent.TwoLocusGenealogy.Total
public import Rhone.Coalescent.Rational.Limit
public import Rhone.MarkovChain.GeneralMutation.RhoZero
public import Rhone.Coalescent.TypedAncestralChain.Sampling
public import Rhone.Coalescent.BranchLengthMoments.Length

@[expose] public section

namespace Rhone.Palomar.SamplingRecursion

open Filter Topology MeasureTheory
open Rhone.Algebra Analysis Coalescent Rhone.LinearAlgebra MarkovChain Probability
open LinearAlgebra.Recursion
  Coalescent.TwoLocusGenealogy Coalescent.TypedAncestralChain Coalescent.BranchLengthMoments
  Algebra.Rational Coalescent.Rational MarkovChain.GeneralMutation

theorem exists_isSolution {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q :=
  Rhone.LinearAlgebra.Recursion.exists_isSolution hθA hθB hρ

theorem isSolution_unique {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolution θA θB ρ πA πB q₁)
    (h₂ : IsSolution θA θB ρ πA πB q₂) : q₁ = q₂ :=
  Rhone.LinearAlgebra.Recursion.IsSolution.unique hθA hθB hρ h₁ h₂

theorem measure_hit_ever_initT {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
    (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    argTrajT θA θB ρ πA πB h ⟨initT n KA KB⟩ {ω | ∃ k, ω k ∈ TFin σA σB}
      = ENNReal.ofReal (Recursion.q (πA := πA) (πB := πB) hθA hθB h.rho
          (cSample σA σB)) :=
  TypedAncestralChain.measure_hit_ever_initT h hθA hθB

theorem sum_q_cSample {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hsA : ∑ i, πA i = 1)
    (hsB : ∑ j, πB j = 1) (n : ℕ) :
    (∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
      Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)) = 1 :=
  TwoLocusGenealogy.sum_q_cSample hθA hθB hρ hsA hsB n

theorem tendsto_q_qHat {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    Tendsto (fun ρ => qAt hθA hθB πA πB ρ ξ) atTop
      (𝓝 (qOne θA πA ξ.mA * qOne θB πB ξ.mB)) :=
  Rational.tendsto_q_qHat hθA hθB hπA hsA hπB hsB ξ

theorem isSolutionOneG_q_rho_zero {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB : F} {νA : Fin KA → F} {νB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB)
    (hπA : ∑ i, νA i = 1) (hπB : ∑ j, νB j = 1) :
    IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB (pimMat νA) (pimMat νB))
      (fun m => Recursion.q (πA := νA) (πB := νB) hθA hθB le_rfl (full m)) :=
  GeneralMutation.isSolutionOneG_q_rho_zero hθA hθB hπA hπB

theorem expected_total_length {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      = ENNReal.ofReal (2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) :=
  BranchLengthMoments.expected_total_length h

end Rhone.Palomar.SamplingRecursion
