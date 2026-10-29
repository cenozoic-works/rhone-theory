/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic

/-! # Symmetry of `E_{i,j}` and its invariance under `s`-preserving specializations of `θ` -/

@[expose] public section

namespace Rhone.Analysis.RareAlleleHierarchy

open LinearAlgebra.Tridiag DenominatorEquation

section Inert

variable {R : Type*} [CommRing R]

theorem dcoefS_symm (i j : ℕ) (s ρ : R) : dcoefS R i j s ρ = dcoefS R j i s ρ := by
  funext t
  simp only [dcoefS]
  rw [Nat.add_comm i j]

theorem bcoef_symm (i j : ℕ) : bcoef R i j = bcoef R j i := by
  funext t
  simp only [bcoef]
  rw [Nat.mul_comm]

theorem ES_symm (i j : ℕ) (s ρ : R) : ES R i j s ρ = ES R j i s ρ := by
  rw [ES_eq_cont, ES_eq_cont, dcoefS_symm, bcoef_symm, Nat.min_comm i j]

theorem E_swap (i j : ℕ) (a b ρ : R) : E R i j a b ρ = E R j i b a ρ := by
  rw [← ES_eq_E i j a b ρ, ← ES_eq_E j i b a ρ, ES_symm i j (a * (i : R) + b * (j : R)) ρ]
  congr 1
  ring

theorem E_transpose_eq (i j : ℕ) (u ρ : R) : E R i j u u ρ = E R j i u u ρ :=
  E_swap i j u u ρ

theorem E_spec_eq {S : Type*} [CommRing S] (φ : R →+* S) (i j : ℕ) (θA θB ρ : R)
    (θA' θB' : S) (h : θA' * (i : S) + θB' * (j : S) = φ (θA * (i : R) + θB * (j : R))) :
    φ (E R i j θA θB ρ) = E S i j θA' θB' (φ ρ) := by
  have hs : φ θA * (i : S) + φ θB * (j : S) = θA' * (i : S) + θB' * (j : S) := by
    rw [h, map_add, map_mul, map_mul, map_natCast, map_natCast]
  rw [E_map φ i j θA θB ρ, ← ES_eq_E i j (φ θA) (φ θB) (φ ρ), hs, ES_eq_E]

end Inert

end Rhone.Analysis.RareAlleleHierarchy
