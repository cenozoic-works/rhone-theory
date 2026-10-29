/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.Operator
public import Rhone.Probability.Denominator.Source

/-! # The source identity `L q̂ = −2 q₁` -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

export Denominator (qHat twoQ1)

section Boundary

theorem qHat_bdry (hθA : θA ≠ 0) (hθB : θB ≠ 0) :
    qHat θA θB πA πB (0 : Config KA KB) = 1
      ∧ (∀ i, qHat θA θB πA πB (Config.eA i : Config KA KB) = πA i)
      ∧ (∀ j, qHat θA θB πA πB (Config.eB j : Config KA KB) = πB j)
      ∧ (∀ i j, qHat θA θB πA πB (Config.eC i j : Config KA KB) = πA i * πB j) := by
  refine ⟨?_, fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · rw [qHat, mA_zero, mB_zero, qOne_zero, qOne_zero, one_mul]
  · rw [qHat, mA_eA, mB_eA, qOne_zero, qOne_eA hθA i, mul_one]
  · rw [qHat, mA_eB, mB_eB, qOne_zero, qOne_eA hθB j, one_mul]
  · rw [qHat, mA_eC, mB_eC, qOne_eA hθA i, qOne_eA hθB j]

theorem Delta_bdry_eq_zero (hθA : θA ≠ 0) (hθB : θB ≠ 0) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) :
    q 0 - qHat θA θB πA πB (0 : Config KA KB) = 0
      ∧ (∀ i, q (Config.eA i) - qHat θA θB πA πB (Config.eA i : Config KA KB) = 0)
      ∧ (∀ j, q (Config.eB j) - qHat θA θB πA πB (Config.eB j : Config KA KB) = 0)
      ∧ (∀ i j, q (Config.eC i j)
          - qHat θA θB πA πB (Config.eC i j : Config KA KB) = 0) := by
  obtain ⟨h0, hA, hB, hC⟩ := qHat_bdry (πA := πA) (πB := πB) hθA hθB
  exact ⟨by rw [hq.empty, h0, sub_self], fun i => by rw [hq.bdryA, hA i, sub_self],
    fun j => by rw [hq.bdryB, hB j, sub_self], fun i j => by rw [hq.bdryC, hC i j, sub_self]⟩

end Boundary

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem source_identity (hθA : 0 < θA) (hθB : 0 < θB) (ξ : Config KA KB) :
    Analysis.RecombinationExpansion.Lop θA θB ρ πA πB (qHat θA θB πA πB) ξ = -twoQ1 θA θB πA πB ξ :=
        by
  rw [Analysis.RecombinationExpansion.Lop, Denominator.source_identity (ρ := ρ) hθA hθB ξ]
  ring

theorem LDelta (hθA : 0 < θA) (hθB : 0 < θB) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    Analysis.RecombinationExpansion.Lop θA θB ρ πA πB (fun η => q η - qHat θA θB πA πB η) ξ = twoQ1
        θA θB πA πB ξ := by
  rw [Analysis.RecombinationExpansion.Lop_sub,
      Analysis.RecombinationExpansion.Lop_eq_zero_of_isSolution hq ξ hn, source_identity hθA hθB ξ]
  ring

end Rhone.Probability.RecombinationExpansion
