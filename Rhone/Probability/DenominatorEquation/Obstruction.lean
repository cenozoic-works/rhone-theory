/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic
public import Rhone.Probability.SlotDeletion.Matrix
public import Rhone.Probability.SlotDeletion.BiallelicDenominator

/-! # Block `(2,2)`: recursion sources at `t = 0` and `t = 1` coincide, so differencing fails -/

@[expose] public section

namespace Rhone.Probability.DenominatorEquation

open Finset Matrix LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open LinearAlgebra.SlotDeletion SlotDeletion LinearAlgebra.Tridiag

section

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem phiRecursionSource_two_two_zero (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    phiRecursionSource q πA πB 2 2 0
      = 2 * kap πA * Phi q πA πB 0 2 0 + 2 * kap πB * Phi q πA πB 2 0 0 := by
  have h12 : Phi q πA πB 1 2 0 = 0 := Phi_i_one hθA hθB hρ hq hπA 2 0
  have h21 : Phi q πA πB 2 1 0 = 0 := Phi_j_one hθA hθB hρ hq hπA hπB 2 0
  rw [phiRecursionSource]
  norm_num [h12, h21]
  ring

theorem phiRecursionSource_two_two_one (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    phiRecursionSource q πA πB 2 2 1
      = 2 * kap πA * Phi q πA πB 0 2 0 + 2 * kap πB * Phi q πA πB 2 0 0 := by
  have h12 : Phi q πA πB 1 2 1 = 0 := Phi_i_one hθA hθB hρ hq hπA 2 1
  have h21 : Phi q πA πB 2 1 1 = 0 := Phi_j_one hθA hθB hρ hq hπA hπB 2 1
  rw [phiRecursionSource]
  norm_num [h12, h21]
  ring

theorem phiRecursionSource_two_two_zero_eq_one (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    phiRecursionSource q πA πB 2 2 0 = phiRecursionSource q πA πB 2 2 1 := by
  rw [phiRecursionSource_two_two_zero hθA hθB hρ hq hπA hπB, phiRecursionSource_two_two_one hθA hθB
      hρ hq hπA hπB]

theorem phiRecursionSource_two_two_one_sub_zero (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    phiRecursionSource q πA πB 2 2 1 - phiRecursionSource q πA πB 2 2 0 = 0 := by
  rw [phiRecursionSource_two_two_zero_eq_one hθA hθB hρ hq hπA hπB, sub_self]

theorem phiRecursionSource_two_two_two (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    phiRecursionSource q πA πB 2 2 2 = 2 * kap πA * kap πB := by
  have h01 : Phi q πA πB 0 1 0 = 0 := Phi_j_one hθA hθB hρ hq hπA hπB 0 0
  have h10 : Phi q πA πB 1 0 0 = 0 := Phi_i_one hθA hθB hρ hq hπA 0 0
  have h11 : Phi q πA πB 1 1 1 = 0 := Phi_i_one hθA hθB hρ hq hπA 1 1
  have h00 : Phi q πA πB 0 0 0 = 1 := Phi_zero_zero hq 0
  rw [phiRecursionSource]
  norm_num [h01, h10, h11, h00]
  ring

end

section Residual

variable {F : Type*} [CommRing F] (θA θB ρ : F)

theorem ell_two_two_top : Analysis.DenominatorEquation.ell F 2 2 θA θB ρ 2 = 16 := by
  have h : min 2 2 = 2 := by norm_num
  have := Analysis.DenominatorEquation.adj_zero_last (R := F) 2 2 θA θB ρ
  rw [h] at this
  rw [this]
  norm_num [Nat.descFactorial]

end Residual

section ResidualR

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem residual_two_two (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    (∑ s ∈ Finset.range 3, Analysis.DenominatorEquation.ell F 2 2 θA θB ρ s * phiRecursionSource q
        πA πB 2 2 s)
      = (Analysis.DenominatorEquation.ell F 2 2 θA θB ρ 0 + Analysis.DenominatorEquation.ell F 2 2
          θA θB ρ 1) * phiRecursionSource q πA πB 2 2 0
        + 32 * kap πA * kap πB := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    ← phiRecursionSource_two_two_zero_eq_one hθA hθB hρ hq hπA hπB, phiRecursionSource_two_two_two
        hθA hθB hρ hq hπA hπB, ell_two_two_top]
  ring

end ResidualR

end Rhone.Probability.DenominatorEquation
