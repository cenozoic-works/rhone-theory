/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Exist
public import Rhone.Probability.Denominator.Swap
public import Rhone.MarkovChain.Biallelic.Unique

/-! # The two-locus general-mutation-matrix recursion -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [CommRing F]

def mutA (ξ : Config KA KB) (i k : Fin KA) : Config KA KB := Probability.Denominator.addA
    (ξ.dropA i) k

def mutB (ξ : Config KA KB) (j l : Fin KB) : Config KA KB := Probability.Denominator.addB
    (ξ.dropB j) l

def mutCA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (k : Fin KA) : Config KA KB :=
  Probability.Denominator.addC (ξ.dropC i j) k j

def mutCB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (l : Fin KB) : Config KA KB :=
  Probability.Denominator.addC (ξ.dropC i j) i l

section Counts

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (k : Fin KA) (l : Fin KB)

@[simp] theorem b_mutA : (mutA ξ i k).b = ξ.b := rfl
@[simp] theorem c_mutA : (mutA ξ i k).c = ξ.c := rfl
@[simp] theorem sumB_mutA : (mutA ξ i k).sumB = ξ.sumB := rfl
@[simp] theorem t_mutA : (mutA ξ i k).t = ξ.t := rfl
@[simp] theorem a_mutB : (mutB ξ j l).a = ξ.a := rfl
@[simp] theorem c_mutB : (mutB ξ j l).c = ξ.c := rfl
@[simp] theorem sumA_mutB : (mutB ξ j l).sumA = ξ.sumA := rfl
@[simp] theorem t_mutB : (mutB ξ j l).t = ξ.t := rfl
@[simp] theorem a_mutCA : (mutCA ξ i j k).a = ξ.a := rfl
@[simp] theorem b_mutCA : (mutCA ξ i j k).b = ξ.b := rfl
@[simp] theorem sumA_mutCA : (mutCA ξ i j k).sumA = ξ.sumA := rfl
@[simp] theorem sumB_mutCA : (mutCA ξ i j k).sumB = ξ.sumB := rfl
@[simp] theorem a_mutCB : (mutCB ξ i j l).a = ξ.a := rfl
@[simp] theorem b_mutCB : (mutCB ξ i j l).b = ξ.b := rfl
@[simp] theorem sumA_mutCB : (mutCB ξ i j l).sumA = ξ.sumA := rfl
@[simp] theorem sumB_mutCB : (mutCB ξ i j l).sumB = ξ.sumB := rfl

theorem sumA_mutA (h : ξ.a i ≠ 0) : (mutA ξ i k).sumA = ξ.sumA := by
  have h1 : (mutA ξ i k).sumA = (∑ x, decf ξ.a i x) + 1 := sum_incf _ _
  have h2 := sum_decf (f := ξ.a) (i := i) h
  have h3 : ξ.sumA = ∑ x, ξ.a x := rfl
  omega

theorem sumB_mutB (h : ξ.b j ≠ 0) : (mutB ξ j l).sumB = ξ.sumB := by
  have h1 : (mutB ξ j l).sumB = (∑ x, decf ξ.b j x) + 1 := sum_incf _ _
  have h2 := sum_decf (f := ξ.b) (i := j) h
  have h3 : ξ.sumB = ∑ x, ξ.b x := rfl
  omega

theorem t_mutCA (h : ξ.c i j ≠ 0) : (mutCA ξ i j k).t = ξ.t := by
  have h1 : (mutCA ξ i j k).t = (∑ x, ∑ y, Config.decC ξ.c i j x y) + 1 :=
    Config.sum_incC _ _ _
  have h2 := Config.sum_decC (m := ξ.c) (i := i) (j := j) h
  have h3 : ξ.t = ∑ x, ∑ y, ξ.c x y := rfl
  omega

theorem t_mutCB (h : ξ.c i j ≠ 0) : (mutCB ξ i j l).t = ξ.t := by
  have h1 : (mutCB ξ i j l).t = (∑ x, ∑ y, Config.decC ξ.c i j x y) + 1 :=
    Config.sum_incC _ _ _
  have h2 := Config.sum_decC (m := ξ.c) (i := i) (j := j) h
  have h3 : ξ.t = ∑ x, ∑ y, ξ.c x y := rfl
  omega

theorem mutA_same (h : ξ.a i ≠ 0) : (mutA ξ i k).nA = ξ.nA ∧ (mutA ξ i k).nB = ξ.nB := by
  have := sumA_mutA ξ i k h
  exact ⟨by simp only [Config.nA, t_mutA]; omega, rfl⟩

theorem mutB_same (h : ξ.b j ≠ 0) : (mutB ξ j l).nA = ξ.nA ∧ (mutB ξ j l).nB = ξ.nB := by
  have := sumB_mutB ξ j l h
  exact ⟨rfl, by simp only [Config.nB, t_mutB]; omega⟩

theorem mutCA_same (h : ξ.c i j ≠ 0) :
    (mutCA ξ i j k).nA = ξ.nA ∧ (mutCA ξ i j k).nB = ξ.nB := by
  have := t_mutCA ξ i j k h
  exact ⟨by simp only [Config.nA, sumA_mutCA]; omega,
    by simp only [Config.nB, sumB_mutCA]; omega⟩

theorem mutCB_same (h : ξ.c i j ≠ 0) :
    (mutCB ξ i j l).nA = ξ.nA ∧ (mutCB ξ i j l).nB = ξ.nB := by
  have := t_mutCB ξ i j l h
  exact ⟨by simp only [Config.nA, sumA_mutCB]; omega,
    by simp only [Config.nB, sumB_mutCB]; omega⟩

theorem n_mutA (h : ξ.a i ≠ 0) : (mutA ξ i k).n = ξ.n := by
  have := sumA_mutA ξ i k h; simp only [Config.n, sumB_mutA, t_mutA]; omega

theorem n_mutB (h : ξ.b j ≠ 0) : (mutB ξ j l).n = ξ.n := by
  have := sumB_mutB ξ j l h; simp only [Config.n, sumA_mutB, t_mutB]; omega

theorem n_mutCA (h : ξ.c i j ≠ 0) : (mutCA ξ i j k).n = ξ.n := by
  have := t_mutCA ξ i j k h; simp only [Config.n, sumA_mutCA, sumB_mutCA]; omega

theorem n_mutCB (h : ξ.c i j ≠ 0) : (mutCB ξ i j l).n = ξ.n := by
  have := t_mutCB ξ i j l h; simp only [Config.n, sumA_mutCB, sumB_mutCB]; omega

end Counts

section Marginals

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (k : Fin KA) (l : Fin KB)

theorem mA_mutA (h : ξ.a i ≠ 0) : (mutA ξ i k).mA = incf (decf ξ.mA i) k := by
  rw [mutA, Probability.Denominator.mA_addA, Config.mA_dropA ξ h]

@[simp] theorem mB_mutA : (mutA ξ i k).mB = ξ.mB := rfl

theorem mB_mutB (h : ξ.b j ≠ 0) : (mutB ξ j l).mB = incf (decf ξ.mB j) l := by
  rw [mutB, Probability.Denominator.mB_addB, Config.mB_dropB ξ h]

@[simp] theorem mA_mutB : (mutB ξ j l).mA = ξ.mA := rfl

theorem mA_mutCA (h : ξ.c i j ≠ 0) : (mutCA ξ i j k).mA = incf (decf ξ.mA i) k := by
  rw [mutCA, Probability.Denominator.mA_addC, Config.mA_dropC ξ h]

theorem mB_mutCA (h : ξ.c i j ≠ 0) : (mutCA ξ i j k).mB = ξ.mB := by
  have hmB : ξ.mB j ≠ 0 := by
    have := Config.cCol_ne_zero ξ i j h
    simp only [Config.mB]; omega
  rw [mutCA, Probability.Denominator.mB_addC, Config.mB_dropC ξ h,
      Probability.Denominator.incf_decf_self hmB]

theorem mB_mutCB (h : ξ.c i j ≠ 0) : (mutCB ξ i j l).mB = incf (decf ξ.mB j) l := by
  rw [mutCB, Probability.Denominator.mB_addC, Config.mB_dropC ξ h]

theorem mA_mutCB (h : ξ.c i j ≠ 0) : (mutCB ξ i j l).mA = ξ.mA := by
  have hmA : ξ.mA i ≠ 0 := by
    have := Config.cRow_ne_zero ξ i j h
    simp only [Config.mA]; omega
  rw [mutCB, Probability.Denominator.mA_addC, Config.mA_dropC ξ h,
      Probability.Denominator.incf_decf_self hmA]

end Marginals

def rhsGen (θA θB ρ : F) (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F)
    (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
    + θA * (∑ i, ∑ k, PA k i * ((ξ.a i : ℕ) : F) * q (mutA ξ i k))
    + θA * (∑ i, ∑ j, ∑ k, PA k i * ((ξ.c i j : ℕ) : F) * q (mutCA ξ i j k))
    + θB * (∑ j, ∑ l, PB l j * ((ξ.b j : ℕ) : F) * q (mutB ξ j l))
    + θB * (∑ i, ∑ j, ∑ l, PB l j * ((ξ.c i j : ℕ) : F) * q (mutCB ξ i j l))
    + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

structure IsSolutionGen (θA θB ρ : F) (νA : Fin KA → F) (νB : Fin KB → F)
    (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F) (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = νA i
  bdryB : ∀ j, q (Config.eB j) = νB j
  bdryC : ∀ i j, q (Config.eC i j) = νA i * νB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
    diag θA θB ρ ξ * q ξ = rhsGen θA θB ρ PA PB q ξ

end Rhone.MarkovChain.GeneralMutation
