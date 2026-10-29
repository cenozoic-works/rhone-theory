/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.Closure.Bridge

/-! # Admissible parameters at which `q` differs from its large-ρ limit, per configuration -/

@[expose] public section

namespace Rhone.Coalescent.Closure

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

theorem exists_admissible_qRho_ne_qHat (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB)
    (ht : 2 ≤ ξ.t) :
    ∃ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
      (∀ i, 0 < πA i) ∧ (∑ i, πA i = 1) ∧ (∀ j, 0 < πB j) ∧ (∑ j, πB j = 1) ∧
      Algebra.Rational.qRho hθA hθB πA πB ξ
        ≠ RatFunc.C (Rhone.Probability.RecombinationExpansion.qHat θA θB πA πB ξ) := by
  obtain ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB, hq1⟩ :=
    exists_admissible_twoQ1_ne_zero hKA hKB ξ ht
  exact ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB,
    Rational.qRho_ne_qHat hθA hθB (fun i => (hπA i).le) hsA (fun j => (hπB j).le) hsB ξ hq1⟩

theorem exists_admissible_q_ne_qHat (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB)
    (ht : 2 ≤ ξ.t) :
    ∃ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
      (∀ i, 0 < πA i) ∧ (∑ i, πA i = 1) ∧ (∀ j, 0 < πB j) ∧ (∑ j, πB j = 1) ∧
      ∃ (ρ : ℝ) (hρ : 0 ≤ ρ),
        LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ
          ≠ Rhone.Probability.RecombinationExpansion.qHat θA θB πA πB ξ := by
  obtain ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB, hq1⟩ :=
    exists_admissible_twoQ1_ne_zero hKA hKB ξ ht
  obtain ⟨ρ, hρ, hne⟩ := Rational.exists_ne_qHat_of_twoQ1_ne_zero hθA hθB
    (fun i => (hπA i).le) hsA (fun j => (hπB j).le) hsB ξ hq1
  refine ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB, ρ, hρ, ?_⟩
  rwa [Rational.qAt_eq_q hθA hθB hρ] at hne

end Rhone.Coalescent.Closure
