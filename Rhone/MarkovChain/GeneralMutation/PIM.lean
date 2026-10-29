/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Exist

/-! # Dual-form cross-validation: the PIM case, as a theorem -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def pimMat (π : Fin KA → F) : Fin KA → Fin KA → F := fun _ i => π i

omit [Field F] [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem pimMat_apply (π : Fin KA → F) (k i : Fin KA) : pimMat π k i = π i := rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem stationary_pimMat (hπ : ∑ i, πA i = 1) (i : Fin KA) :
    ∑ k, πA k * pimMat πA k i = πA i := by
  simp only [pimMat_apply, ← Finset.sum_mul, hπ, one_mul]

variable {q : Config KA KB → F}

theorem sum_mutA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (i : Fin KA) :
    (∑ k, q (mutA ξ i k)) = q (ξ.dropA i) :=
  Probability.Denominator.marginalise_A hθA hθB hρ hπA hq (ξ.dropA i)

theorem sum_mutCA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    (∑ k, q (mutCA ξ i j k)) = q (ξ.killA i j) :=
  Probability.Denominator.marginalise_C hθA hθB hρ hπA hq (ξ.dropC i j) j

theorem sum_mutB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπB : ∑ j, πB j = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (j : Fin KB) :
    (∑ l, q (mutB ξ j l)) = q (ξ.dropB j) :=
  Probability.Denominator.marginalise_B hθA hθB hρ hπB hq (ξ.dropB j)

theorem sum_mutCB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπB : ∑ j, πB j = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    (∑ l, q (mutCB ξ i j l)) = q (ξ.killB i j) :=
  Probability.Denominator.marginalise_C' hθA hθB hρ hπB hq (ξ.dropC i j) i

theorem rhsGen_eq_rhs (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) :
    rhsGen θA θB ρ (pimMat πA) (pimMat πB) q ξ = rhs θA θB ρ πA πB q ξ := by
  have e1 : (∑ i, ∑ k, pimMat πA k i * ((ξ.a i : ℕ) : F) * q (mutA ξ i k))
      = ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pimMat_apply]
    rw [← Finset.mul_sum, sum_mutA hθA hθB hρ hπA hq ξ i]
    ring
  have e2 : (∑ i, ∑ j, ∑ k, pimMat πA k i * ((ξ.c i j : ℕ) : F) * q (mutCA ξ i j k))
      = ∑ i, πA i * (∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pimMat_apply]
    rw [← Finset.mul_sum, sum_mutCA hθA hθB hρ hπA hq ξ i j]
    ring
  have e3 : (∑ j, ∑ l, pimMat πB l j * ((ξ.b j : ℕ) : F) * q (mutB ξ j l))
      = ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pimMat_apply]
    rw [← Finset.mul_sum, sum_mutB hθA hθB hρ hπB hq ξ j]
    ring
  have e4 : (∑ i, ∑ j, ∑ l, pimMat πB l j * ((ξ.c i j : ℕ) : F) * q (mutCB ξ i j l))
      = ∑ j, πB j * (∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pimMat_apply]
    rw [← Finset.mul_sum, sum_mutCB hθA hθB hρ hπB hq ξ i j]
    ring
  have eA : θA * (∑ i, ∑ k, pimMat πA k i * ((ξ.a i : ℕ) : F) * q (mutA ξ i k))
      + θA * (∑ i, ∑ j, ∑ k, pimMat πA k i * ((ξ.c i j : ℕ) : F) * q (mutCA ξ i j k))
      = θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)) := by
    rw [e1, e2, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have eB : θB * (∑ j, ∑ l, pimMat πB l j * ((ξ.b j : ℕ) : F) * q (mutB ξ j l))
      + θB * (∑ i, ∑ j, ∑ l, pimMat πB l j * ((ξ.c i j : ℕ) : F) * q (mutCB ξ i j l))
      = θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)) := by
    rw [e3, e4, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [rhsGen, rhs]
  linarith [eA, eB]

theorem IsSolution.isSolutionGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hq : IsSolution θA θB ρ πA πB q) :
    IsSolutionGen θA θB ρ πA πB (pimMat πA) (pimMat πB) q where
  empty := hq.empty
  bdryA := hq.bdryA
  bdryB := hq.bdryB
  bdryC := hq.bdryC
  recursion ξ hn := by
    rw [rhsGen_eq_rhs hθA hθB hρ hπA hπB hq ξ]
    exact hq.recursion ξ hn

theorem isSolutionGen_iff (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπApos : ∀ i, 0 < πA i) (hπBpos : ∀ j, 0 < πB j)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (q : Config KA KB → F) :
    IsSolutionGen θA θB ρ πA πB (pimMat πA) (pimMat πB) q ↔ IsSolution θA θB ρ πA πB q := by
  constructor
  · intro hgen
    have h0 := LinearAlgebra.Recursion.q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
    have h0gen := IsSolution.isSolutionGen hθA hθB hρ hπA hπB h0
    have : q = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ :=
      IsSolutionGen.unique hθA hθB hρ (fun _k i => (hπApos i).le) (fun _l j => (hπBpos j).le)
        hπApos hπBpos (stationary_pimMat hπA) (stationary_pimMat hπB) hgen h0gen
    rw [this]
    exact h0
  · exact IsSolution.isSolutionGen hθA hθB hρ hπA hπB

theorem qGen_eq_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπApos : ∀ i, 0 < πA i) (hπBpos : ∀ j, 0 < πB j)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) :
    qGen (νA := πA) (νB := πB) (PA := pimMat πA) (PB := pimMat πB) hθA hθB hρ
        (fun _k i => (hπApos i).le) (fun _l j => (hπBpos j).le) hπApos hπBpos
        (stationary_pimMat hπA) (stationary_pimMat hπB)
      = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ := by
  have hgen := qGen_isSolutionGen (νA := πA) (νB := πB) (PA := pimMat πA) (PB := pimMat πB)
    hθA hθB hρ (fun _k i => (hπApos i).le) (fun _l j => (hπBpos j).le) hπApos hπBpos
    (stationary_pimMat hπA) (stationary_pimMat hπB)
  have := (isSolutionGen_iff hθA hθB hρ hπApos hπBpos hπA hπB _).mp hgen
  exact LinearAlgebra.Recursion.q_unique hθA hθB hρ this

end Rhone.MarkovChain.GeneralMutation
