module

public import Rhone.Probability.ExplicitFormula.Main
public import Rhone.Probability.AlleleLumping.Lumping
public import Rhone.Probability.BooleanLatticeInverse.ExplicitBiallelicSampling

@[expose] public section

namespace Rhone.Palomar.ExplicitFormula

open Finset LinearAlgebra.Recursion LinearAlgebra.ExplicitFormula Probability.ExplicitFormula
    LinearAlgebra.AlleleLumping Probability.AlleleLumping

theorem q_eq_qExplicit {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config 2 2) :
    q ξ = qExplicit θA θB ρ πA πB ξ :=
  Rhone.Probability.ExplicitFormula.q_eq_qExplicit hθA hθB hρ hπA hπB hq ξ

theorem qExplicit_isSolution {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    IsSolution θA θB ρ πA πB (qExplicit θA θB ρ πA πB) :=
  Rhone.Probability.ExplicitFormula.qExplicit_isSolution hθA hθB hρ hπA hπB

theorem lump_isSolution {KA KB KA' KB' : ℕ} {F : Type*} [Field F] [CharZero F]
    {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F} {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q)
    (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB')
    (S : Config KA' KB' → Finset (Config KA KB))
    (hS : ∀ η ξ, ξ ∈ S η ↔ push fA fB ξ = η) :
    IsSolution θA θB ρ (pushPi fA πA) (pushPi fB πB)
      (fun η => (mult η : F)⁻¹ * ∑ ξ ∈ S η, (mult ξ : F) * q ξ) := by
  have h : (fun η => (mult η : F)⁻¹ * ∑ ξ ∈ S η, (mult ξ : F) * q ξ) = lump fA fB q := by
    funext η
    have hη : S η = fibre fA fB η := Finset.ext fun ξ => (hS η ξ).trans mem_fibre.symm
    rw [lump, lumpSum, hη]
  rw [h]
  exact Rhone.Probability.AlleleLumping.lump_isSolution hq fA fB

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
  have hη : S = fibre fA fB η := Finset.ext fun ξ => (hS ξ).trans mem_fibre.symm
  rw [hη]
  exact Rhone.Probability.AlleleLumping.lumping_eq_qExplicit hθA hθB hρ hπA hπB hq fA fB η

section KB2

open LinearAlgebra.BooleanLatticeInverse Probability.BooleanLatticeInverse

theorem q_eq_qExplicitKB2 {KA : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F} {q : Config KA 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA 2) :
    q ξ = qExplicitKB2 θA θB ρ πA πB ξ :=
  Rhone.Probability.BooleanLatticeInverse.q_eq_qExplicitKB2 hθA hθB hρ hπA hπB hq ξ

end KB2

end Rhone.Palomar.ExplicitFormula
