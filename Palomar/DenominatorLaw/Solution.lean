module

public import Rhone.LinearAlgebra.Tridiag.RhoDegree
public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive
public import Rhone.Probability.SlotDeletion.Matrix
public import Rhone.Probability.SlotDeletion.Surj
public import Rhone.Probability.Denominator.SharpnessTransfer
public import Rhone.Analysis.DiagonalObstruction.Unbounded
public import Rhone.Probability.RecombinationDegree.MutationCoordinates

@[expose] public section

namespace Rhone.Palomar.DenominatorLaw

open Polynomial Rhone.Algebra Analysis Rhone.LinearAlgebra Probability LinearAlgebra.Tridiag
  LinearAlgebra.Recursion LinearAlgebra.Multilinear Probability.Multilinear
  LinearAlgebra.SlotDeletion Probability.SlotDeletion Algebra.Denominator Probability.Denominator
open scoped Matrix

theorem T_mulVec_Phi_eq_phiRecursionSource {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j : ℕ) :
    Tridiag.T F i j θA θB ρ *ᵥ (fun t : Fin (min i j + 1) => Phi q πA πB i j (t : ℕ))
      = fun t : Fin (min i j + 1) => phiRecursionSource q πA πB i j (t : ℕ) :=
  SlotDeletion.T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j

theorem Dfull_mul_q_mem {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} {πA πB : Fin 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (ξ : Config 2 2) :
    Dfull θA θB ρ ξ.nA ξ.nB * q ξ ∈ A :=
  SlotDeletion.Dfull_mul_q_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ

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
    DvdIn A (Tridiag.E F ξ.nA ξ.nB θA θB ρ) d :=
  Denominator.dvdIn_E_of_clears hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ hiA hiB hH hd

theorem natDegree_E {F : Type*} [CommRing F] (i j : ℕ) (a b : F)
    (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j :=
  Tridiag.natDegree_E i j a b h

theorem E_pos {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F] {i j : ℕ}
    {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j) (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    0 < E F i j θA θB ρ :=
  GaloisDegreeSeven.E_pos hi hj hA hB hρ

theorem unbounded_irreducible_E_mm_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m X 0 (C RatFunc.X) ∧
      D < G.natDegree :=
  DiagonalObstruction.unbounded_irreducible_E_mm_factor_degree D

theorem unbounded_irreducible_E_mm_recombination_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m (C RatFunc.X) 0 X ∧
      D < G.natDegree := by
  obtain ⟨m, hm, G, hirr, hdiv, -, hdeg⟩ :=
    RecombinationDegree.unbounded_surviving_recombination_factor D
  exact ⟨m, hm, G, hirr, hdiv, hdeg⟩

end Rhone.Palomar.DenominatorLaw
