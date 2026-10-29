/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Closure.MatchingGeneratingFunction
public import Rhone.Probability.SlotDeletion.Source
public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani
public import Rhone.LinearAlgebra.Tridiag.Defs

/-! # The explicit block-by-block formula: definitions -/

@[expose] public section

namespace Rhone.Probability.ExplicitFormula

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear Closure

variable {F : Type*} [Field F]

noncomputable def srcR (κA γA κB γB : F) (Ψ : ℕ → ℕ → ℕ → F) (i j t : ℕ) : F :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : F) * Ψ (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : F) * Ψ (i - 2) j (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : F) * Ψ (i - 1) j t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : F) * Ψ i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : F) * Ψ i (j - 2) (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : F) * Ψ i (j - 1) t
    + ((t * (t - 1) : ℕ) : F) * (κA * κB * Ψ (i - 2) (j - 2) (t - 2)
      + κA * γB * Ψ (i - 2) (j - 1) (t - 2)
      + γA * κB * Ψ (i - 1) (j - 2) (t - 2)
      + γA * γB * Ψ (i - 1) (j - 1) (t - 1))

noncomputable def PhiTab (θA θB ρ : F) (πA πB : Fin 2 → F) : ℕ → ℕ → ℕ → ℕ → F
  | 0,   _, _, _ => 1
  | n+1, i, j, t =>
    if i = 0 ∧ j = 0 then 1 else
      (LinearAlgebra.Tridiag.E F i j θA θB ρ)⁻¹ *
        ∑ s ∈ Finset.range (min i j + 1),
          LinearAlgebra.RecombinationExpansion.usmaniEntry
              (LinearAlgebra.Tridiag.dcoef F i j θA θB ρ) (LinearAlgebra.Tridiag.bcoef F i j)
              (LinearAlgebra.Tridiag.ccoef F ρ) (min i j + 1) (min t (min i j)) s
            * srcR (kap πA) (gam πA) (kap πB) (gam πB) (PhiTab θA θB ρ πA πB n) i j s

noncomputable def PhiX (θA θB ρ : F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  PhiTab θA θB ρ πA πB (i + j) i j t

noncomputable def qExplicit (θA θB ρ : F) (πA πB : Fin 2 → F) (ξ : Config 2 2) : F :=
  ∑ d1 ∈ Finset.range (ξ.nA + 1), ∑ d2 ∈ Finset.range (ξ.nB + 1),
    ∑ d3 ∈ Finset.range (ξ.t + 1),
      (Gcfg πA πB ξ).coeff (mono3 d1 d2 d3) * PhiX θA θB ρ πA πB d1 d2 d3

theorem phiRecursionSource_eq_srcR (q : Config 2 2 → F) (πA πB : Fin 2 → F) :
    SlotDeletion.phiRecursionSource q πA πB
      = srcR (kap πA) (gam πA) (kap πB) (gam πB) (Phi q πA πB) := rfl

end Rhone.Probability.ExplicitFormula
