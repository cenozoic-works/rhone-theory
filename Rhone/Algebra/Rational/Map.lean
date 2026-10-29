/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Exist

/-! # Naturality of the killed-PIM recursion under ring homomorphisms -/

@[expose] public section

namespace Rhone.Algebra.Rational

open LinearAlgebra.Recursion

variable {KA KB : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem diag_map (φ : R →+* S) (θA θB ρ : R) (ξ : Config KA KB) :
    φ (diag θA θB ρ ξ) = diag (φ θA) (φ θB) (φ ρ) ξ := by
  simp only [diag, map_add, map_mul, map_natCast]

theorem rhs_map (φ : R →+* S) (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R)
    (q : Config KA KB → R) (ξ : Config KA KB) :
    φ (rhs θA θB ρ πA πB q ξ)
      = rhs (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
          (fun η => φ (q η)) ξ := by
  simp only [rhs, map_add, map_mul, map_sum, map_natCast]

theorem isSolution_map (φ : R →+* S) {θA θB ρ : R} {πA : Fin KA → R} {πB : Fin KB → R}
    {q : Config KA KB → R} (h : IsSolution θA θB ρ πA πB q) :
    IsSolution (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
      (fun η => φ (q η)) where
  empty := by rw [← map_one φ, h.empty]
  bdryA i := by rw [h.bdryA i]
  bdryB j := by rw [h.bdryB j]
  bdryC i j := by rw [h.bdryC i j, map_mul]
  recursion ξ hn := by
    rw [← diag_map φ, ← map_mul, h.recursion ξ hn, rhs_map φ]

end Rhone.Algebra.Rational
