/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Marginal

/-! # The locus swap, and marginalization on the B side -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ}

def swapC (ξ : Config KA KB) : Config KB KA := ⟨ξ.b, ξ.a, fun j i => ξ.c i j⟩

@[simp] theorem swapC_swapC (ξ : Config KA KB) : swapC (swapC ξ) = ξ := rfl

theorem decC_transpose (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    Config.decC (fun j' i' => m i' j') j i = fun j' i' => Config.decC m i j i' j' := by
  funext y x
  simp only [decC_apply]
  by_cases h1 : x = i <;> by_cases h2 : y = j <;> simp_all

theorem incC_transpose (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    Config.incC (fun j' i' => m i' j') j i = fun j' i' => Config.incC m i j i' j' := by
  funext y x
  simp only [incC_apply]
  by_cases h1 : x = i <;> by_cases h2 : y = j <;> simp_all

section Basic

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)

@[simp] theorem sumA_swapC : (swapC ξ).sumA = ξ.sumB := rfl
@[simp] theorem sumB_swapC : (swapC ξ).sumB = ξ.sumA := rfl
@[simp] theorem cRow_swapC : (swapC ξ).cRow j = ξ.cCol j := rfl
@[simp] theorem cCol_swapC : (swapC ξ).cCol i = ξ.cRow i := rfl
@[simp] theorem coalA_swapC : (swapC ξ).coalA j = ξ.coalB j := rfl
@[simp] theorem coalB_swapC : (swapC ξ).coalB i = ξ.coalA i := rfl
@[simp] theorem coalC_swapC : (swapC ξ).coalC j i = ξ.coalC i j := rfl

theorem coalAB_swapC : (swapC ξ).coalAB j i = ξ.coalAB i j := by
  simp only [Config.coalAB, swapC]
  ring

theorem t_swapC : (swapC ξ).t = ξ.t := Finset.sum_comm

theorem nA_swapC : (swapC ξ).nA = ξ.nB := by
  simp only [Config.nA, Config.nB, sumA_swapC, t_swapC]

theorem nB_swapC : (swapC ξ).nB = ξ.nA := by
  simp only [Config.nA, Config.nB, sumB_swapC, t_swapC]

theorem n_swapC : (swapC ξ).n = ξ.n := by
  simp only [Config.n, sumA_swapC, sumB_swapC, t_swapC]
  omega

@[simp] theorem dropA_swapC : (swapC ξ).dropA j = swapC (ξ.dropB j) := rfl
@[simp] theorem dropB_swapC : (swapC ξ).dropB i = swapC (ξ.dropA i) := rfl

theorem dropC_swapC : (swapC ξ).dropC j i = swapC (ξ.dropC i j) :=
  Config.ext rfl rfl (decC_transpose ξ.c i j)

theorem mergeAB_swapC : (swapC ξ).mergeAB j i = swapC (ξ.mergeAB i j) :=
  Config.ext rfl rfl (incC_transpose ξ.c i j)

theorem killA_swapC : (swapC ξ).killA j i = swapC (ξ.killB i j) :=
  Config.ext rfl rfl (decC_transpose ξ.c i j)

theorem killB_swapC : (swapC ξ).killB j i = swapC (ξ.killA i j) :=
  Config.ext rfl rfl (decC_transpose ξ.c i j)

theorem split_swapC : (swapC ξ).split j i = swapC (ξ.split i j) :=
  Config.ext rfl rfl (decC_transpose ξ.c i j)

@[simp] theorem swapC_zero : swapC (0 : Config KA KB) = 0 := rfl

@[simp] theorem swapC_eA : swapC (Config.eA i : Config KA KB) = Config.eB i := rfl

@[simp] theorem swapC_eB : swapC (Config.eB j : Config KA KB) = Config.eA j := rfl

@[simp] theorem swapC_eC : swapC (Config.eC i j : Config KA KB) = Config.eC j i :=
  Config.ext rfl rfl (incC_transpose (fun _ _ => 0) i j).symm

theorem swapC_addA_swapC : swapC (addA (swapC ξ) j) = addB ξ j := rfl

theorem swapC_addB_swapC : swapC (addB (swapC ξ) i) = addA ξ i := rfl

theorem swapC_addC_swapC : swapC (addC (swapC ξ) j i) = addC ξ i j :=
  Config.ext rfl rfl (by
    funext x y
    have := incC_transpose ξ.c i j
    simp only [swapC, addC]
    exact congrFun (congrFun this y) x)

end Basic

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem diag_swapC (θA θB ρ : F) (ξ : Config KA KB) :
    diag θB θA ρ (swapC ξ) = diag θA θB ρ ξ := by
  simp only [LinearAlgebra.Recursion.diag, n_swapC, nA_swapC, nB_swapC, t_swapC]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem rhs_swapC (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) (ξ : Config KA KB) :
    rhs θB θA ρ πB πA (fun η : Config KB KA => q (swapC η)) (swapC ξ)
      = rhs θA θB ρ πA πB q ξ := by
  have L1 : (∑ j, (((swapC ξ).coalA j : ℕ) : F) * q (swapC ((swapC ξ).dropA j)))
      = ∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j) := rfl
  have L2 : (∑ i, (((swapC ξ).coalB i : ℕ) : F) * q (swapC ((swapC ξ).dropB i)))
      = ∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i) := rfl
  have L3 : (∑ j, ∑ i, (((swapC ξ).coalC j i : ℕ) : F) * q (swapC ((swapC ξ).dropC j i)))
      = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [dropC_swapC, swapC_swapC, coalC_swapC]
  have L4 : (∑ j, ∑ i, (((swapC ξ).coalAB j i : ℕ) : F) * q (swapC ((swapC ξ).mergeAB j i)))
      = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mergeAB_swapC, swapC_swapC, coalAB_swapC]
  have L5 : (θB * ∑ j, πB j * ((((swapC ξ).a j : ℕ) : F) * q (swapC ((swapC ξ).dropA j))
        + ∑ i, (((swapC ξ).c j i : ℕ) : F) * q (swapC ((swapC ξ).killA j i))))
      = θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)) := by
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      congr 1
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [killA_swapC, swapC_swapC]; rfl
  have L6 : (θA * ∑ i, πA i * ((((swapC ξ).b i : ℕ) : F) * q (swapC ((swapC ξ).dropB i))
        + ∑ j, (((swapC ξ).c j i : ℕ) : F) * q (swapC ((swapC ξ).killB j i))))
      = θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)) := by
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      congr 1
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [killB_swapC, swapC_swapC]; rfl
  have L7 : (ρ * ∑ j, ∑ i, (((swapC ξ).c j i : ℕ) : F) * q (swapC ((swapC ξ).split j i)))
      = ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j) := by
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [split_swapC, swapC_swapC]; rfl
  simp only [rhs]
  rw [L1, L2, L3, L4, L5, L6, L7]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem isSolution_swap {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) :
    IsSolution θB θA ρ πB πA (fun η : Config KB KA => q (swapC η)) where
  empty := by simpa using hq.empty
  bdryA j := by simpa using hq.bdryB j
  bdryB i := by simpa using hq.bdryA i
  bdryC j i := by rw [swapC_eC, hq.bdryC i j]; ring
  recursion η hn := by
    have hη : η = swapC (swapC η) := rfl
    rw [hη, diag_swapC, rhs_swapC θA θB ρ πA πB q (swapC η)]
    exact hq.recursion (swapC η) (by rwa [n_swapC])

theorem marginalise_B (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπB : ∑ j, πB j = 1)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) :
    (∑ j, q (addB ξ j)) = q ξ := by
  have h := marginalise_A hθB hθA hρ hπB (isSolution_swap hq) (swapC ξ)
  simp only [swapC_addA_swapC, swapC_swapC] at h
  exact h

theorem marginalise_C' (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπB : ∑ j, πB j = 1)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (i : Fin KA) :
    (∑ j, q (addC ξ i j)) = q (addA ξ i) := by
  have h := marginalise_C hθB hθA hρ hπB (isSolution_swap hq) (swapC ξ) i
  simp only [swapC_addC_swapC, swapC_addB_swapC] at h
  exact h

end Rhone.Probability.Denominator
