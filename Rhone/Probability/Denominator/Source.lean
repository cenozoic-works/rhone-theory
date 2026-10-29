/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.OneLocus
public import Rhone.LinearAlgebra.Recursion.Bookkeeping

/-! # The source identity: `L q̂ = −2 q₁` -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def qHat (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (ξ : Config KA KB) : F :=
  qOne θA πA ξ.mA * qOne θB πB ξ.mB

def twoQ1 (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (ξ : Config KA KB) : F :=
  ((ξ.t * (ξ.t - 1) : ℕ) : F) * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
    - qOne θB πB ξ.mB * ∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i)
    - qOne θA πA ξ.mA * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j)
    + ∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
        * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j))

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_killA_qHat (ξ : Config KA KB) (i : Fin KA) :
    (∑ j, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killA i j))
      = ((ξ.cRow i : ℕ) : F) * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB) := by
  have hterm : ∀ j : Fin KB, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killA i j)
      = ((ξ.c i j : ℕ) : F) * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB) := by
    intro j
    by_cases h : ξ.c i j = 0
    · rw [h]; simp
    · rw [qHat, Config.mA_killA ξ h, Config.mB_killA ξ h]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, ← Finset.sum_mul,
    ← Nat.cast_sum]
  rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_killB_qHat (ξ : Config KA KB) (j : Fin KB) :
    (∑ i, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killB i j))
      = ((ξ.cCol j : ℕ) : F) * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)) := by
  have hterm : ∀ i : Fin KA, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killB i j)
      = ((ξ.c i j : ℕ) : F) * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)) := by
    intro i
    by_cases h : ξ.c i j = 0
    · rw [h]; simp
    · rw [qHat, Config.mA_killB ξ h, Config.mB_killB ξ h]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, ← Finset.sum_mul,
    ← Nat.cast_sum]
  rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_A_line_gen (ξ : Config KA KB) (hdenA : rising θA ξ.nA ≠ 0) :
    (∑ i, ((ξ.coalA i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i))
      + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killA i j))
      = (((ξ.nA * (ξ.nA - 1) : ℕ) : F) + θA * ((ξ.nA : ℕ) : F))
          * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
        - (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i))
          * qOne θB πB ξ.mB := by
  have hdropA : ∀ i : Fin KA, ((ξ.a i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
      = ((ξ.a i : ℕ) : F) * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB) := by
    intro i
    by_cases h : ξ.a i = 0
    · rw [h]; simp
    · rw [qHat, Config.mA_dropA ξ h, Config.mB_dropA]
  have hcoalA : ∀ i : Fin KA, ((ξ.coalA i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
      = ((ξ.coalA i : ℕ) : F) * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB) := by
    intro i
    by_cases h : ξ.a i = 0
    · rw [ξ.coalA_eq_zero_of h]; simp
    · rw [qHat, Config.mA_dropA ξ h, Config.mB_dropA]
  have hper : ∀ i : Fin KA, ((ξ.coalA i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
      + θA * (πA i * (((ξ.a i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killA i j)))
      = (((ξ.coalA i : ℕ) : F) + θA * πA i * ((ξ.mA i : ℕ) : F))
        * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB) := by
    intro i
    rw [hcoalA i, hdropA i, sum_killA_qHat ξ i]
    have hm : ((ξ.mA i : ℕ) : F) = ((ξ.a i : ℕ) : F) + ((ξ.cRow i : ℕ) : F) := by
      rw [show ξ.mA i = ξ.a i + ξ.cRow i from rfl]; push_cast; ring
    rw [hm]; ring
  have hbook : ∀ i : Fin KA, ((ξ.coalA i : ℕ) : F)
      = ((ξ.mA i * (ξ.mA i - 1) : ℕ) : F) - ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) := by
    intro i
    have hb : ξ.coalA i + ξ.cRow i * (ξ.cRow i - 1) = ξ.mA i * (ξ.mA i - 1) :=
      ξ.bookkeeping_coalA i
    have : ((ξ.coalA i : ℕ) : F) + ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F)
        = ((ξ.mA i * (ξ.mA i - 1) : ℕ) : F) := by exact_mod_cast congrArg (Nat.cast : ℕ → F) hb
    linear_combination this
  have hrec := qOne_recursion_gen (θ := θA) (π := πA) ξ.mA
    (by rw [Config.sum_mA]; exact hdenA)
  rw [Config.sum_mA] at hrec
  have main : (∑ i, (((ξ.coalA i : ℕ) : F) + θA * πA i * ((ξ.mA i : ℕ) : F))
        * (qOne θA πA (decf ξ.mA i) * qOne θB πB ξ.mB))
      = (∑ i, (((ξ.mA i * (ξ.mA i - 1) : ℕ) : F) + θA * πA i * ((ξ.mA i : ℕ) : F))
          * qOne θA πA (decf ξ.mA i)) * qOne θB πB ξ.mB
        - (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i))
          * qOne θB πB ξ.mB := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hbook i]; ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hper i, main, ← hrec]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_B_line_gen (ξ : Config KA KB) (hdenB : rising θB ξ.nB ≠ 0) :
    (∑ j, ((ξ.coalB j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j))
      + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killB i j))
      = (((ξ.nB * (ξ.nB - 1) : ℕ) : F) + θB * ((ξ.nB : ℕ) : F))
          * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
        - qOne θA πA ξ.mA
          * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j) := by
  have hdropB : ∀ j : Fin KB, ((ξ.b j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
      = ((ξ.b j : ℕ) : F) * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)) := by
    intro j
    by_cases h : ξ.b j = 0
    · rw [h]; simp
    · rw [qHat, Config.mA_dropB, Config.mB_dropB ξ h]
  have hcoalB : ∀ j : Fin KB, ((ξ.coalB j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
      = ((ξ.coalB j : ℕ) : F) * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)) := by
    intro j
    by_cases h : ξ.b j = 0
    · rw [ξ.coalB_eq_zero_of h]; simp
    · rw [qHat, Config.mA_dropB, Config.mB_dropB ξ h]
  have hper : ∀ j : Fin KB, ((ξ.coalB j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
      + θB * (πB j * (((ξ.b j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killB i j)))
      = (((ξ.coalB j : ℕ) : F) + θB * πB j * ((ξ.mB j : ℕ) : F))
        * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)) := by
    intro j
    rw [hcoalB j, hdropB j, sum_killB_qHat ξ j]
    have hm : ((ξ.mB j : ℕ) : F) = ((ξ.b j : ℕ) : F) + ((ξ.cCol j : ℕ) : F) := by
      rw [show ξ.mB j = ξ.b j + ξ.cCol j from rfl]; push_cast; ring
    rw [hm]; ring
  have hbook : ∀ j : Fin KB, ((ξ.coalB j : ℕ) : F)
      = ((ξ.mB j * (ξ.mB j - 1) : ℕ) : F) - ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) := by
    intro j
    have hb : ξ.coalB j + ξ.cCol j * (ξ.cCol j - 1) = ξ.mB j * (ξ.mB j - 1) :=
      ξ.bookkeeping_coalB j
    have : ((ξ.coalB j : ℕ) : F) + ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F)
        = ((ξ.mB j * (ξ.mB j - 1) : ℕ) : F) := by exact_mod_cast congrArg (Nat.cast : ℕ → F) hb
    linear_combination this
  have hrec := qOne_recursion_gen (θ := θB) (π := πB) ξ.mB
    (by rw [Config.sum_mB]; exact hdenB)
  rw [Config.sum_mB] at hrec
  have main : (∑ j, (((ξ.coalB j : ℕ) : F) + θB * πB j * ((ξ.mB j : ℕ) : F))
        * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j)))
      = qOne θA πA ξ.mA * (∑ j, (((ξ.mB j * (ξ.mB j - 1) : ℕ) : F)
          + θB * πB j * ((ξ.mB j : ℕ) : F)) * qOne θB πB (decf ξ.mB j))
        - qOne θA πA ξ.mA
          * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hbook j]; ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hper j, main, ← hrec]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_C_line (ξ : Config KA KB) :
    (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * qHat θA θB πA πB (ξ.dropC i j))
      = ∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
          * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j)) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ξ.c i j = 0
  · rw [ξ.coalC_eq_zero_of h, h]; simp
  · rw [qHat, Config.mA_dropC ξ h, Config.mB_dropC ξ h]
    rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_merge_line (ξ : Config KA KB) :
    (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * qHat θA θB πA πB (ξ.mergeAB i j))
      = ((2 * (ξ.sumA * ξ.sumB) : ℕ) : F) * qHat θA θB πA πB ξ := by
  have hterm : ∀ (i : Fin KA) (j : Fin KB),
      ((ξ.coalAB i j : ℕ) : F) * qHat θA θB πA πB (ξ.mergeAB i j)
        = ((ξ.coalAB i j : ℕ) : F) * qHat θA θB πA πB ξ := by
    intro i j
    by_cases ha : ξ.a i = 0
    · rw [ξ.coalAB_eq_zero_left j ha]; simp
    by_cases hb : ξ.b j = 0
    · rw [ξ.coalAB_eq_zero_right i hb]; simp
    · rw [qHat, qHat, Config.mA_mergeAB ξ j ha, Config.mB_mergeAB ξ i hb]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
  simp only [← Finset.sum_mul, ← Nat.cast_sum]
  rw [Config.sum_coalAB]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_split_line (ξ : Config KA KB) :
    (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.split i j))
      = ((ξ.t : ℕ) : F) * qHat θA θB πA πB ξ := by
  have hterm : ∀ (i : Fin KA) (j : Fin KB),
      ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.split i j)
        = ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB ξ := by
    intro i j
    by_cases h : ξ.c i j = 0
    · rw [h]; simp
    · rw [qHat, qHat, Config.mA_split ξ h, Config.mB_split ξ h]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
  simp only [← Finset.sum_mul, ← Nat.cast_sum]
  rw [Config.sum_c]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem source_identity_gen (ξ : Config KA KB) (hdenA : rising θA ξ.nA ≠ 0)
    (hdenB : rising θB ξ.nB ≠ 0) :
    rhs θA θB ρ πA πB (qHat θA θB πA πB) ξ
      = diag θA θB ρ ξ * qHat θA θB πA πB ξ + twoQ1 θA θB πA πB ξ := by
  have hbk : ((ξ.n * (ξ.n - 1) : ℕ) : F) + ((ξ.t * (ξ.t - 1) : ℕ) : F)
      = ((ξ.nA * (ξ.nA - 1) : ℕ) : F) + ((ξ.nB * (ξ.nB - 1) : ℕ) : F)
        + ((2 * (ξ.sumA * ξ.sumB) : ℕ) : F) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → F) ξ.bookkeeping_diag
  have e1 := sum_A_line_gen (θB := θB) (πA := πA) (πB := πB) ξ hdenA
  have e2 := sum_B_line_gen (θA := θA) (πA := πA) (πB := πB) ξ hdenB
  have e3 := sum_C_line (θA := θA) (θB := θB) (πA := πA) (πB := πB) ξ
  have e4 := sum_merge_line (θA := θA) (θB := θB) (πA := πA) (πB := πB) ξ
  have e5 := sum_split_line (θA := θA) (θB := θB) (πA := πA) (πB := πB) ξ
  simp only [rhs, LinearAlgebra.Recursion.diag, twoQ1, qHat] at *
  linear_combination e1 + e2 + e3 + e4 + ρ * e5
    - (qOne θA πA ξ.mA * qOne θB πB ξ.mB) * hbk

theorem sum_A_line (hθA : 0 < θA) (ξ : Config KA KB) :
    (∑ i, ((ξ.coalA i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i))
      + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * qHat θA θB πA πB (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killA i j))
      = (((ξ.nA * (ξ.nA - 1) : ℕ) : F) + θA * ((ξ.nA : ℕ) : F))
          * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
        - (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i))
          * qOne θB πB ξ.mB :=
  sum_A_line_gen ξ (rising_ne_zero hθA _)

theorem sum_B_line (hθB : 0 < θB) (ξ : Config KA KB) :
    (∑ j, ((ξ.coalB j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j))
      + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * qHat θA θB πA πB (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : F) * qHat θA θB πA πB (ξ.killB i j))
      = (((ξ.nB * (ξ.nB - 1) : ℕ) : F) + θB * ((ξ.nB : ℕ) : F))
          * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
        - qOne θA πA ξ.mA
          * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j) :=
  sum_B_line_gen ξ (rising_ne_zero hθB _)

theorem source_identity (hθA : 0 < θA) (hθB : 0 < θB) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (qHat θA θB πA πB) ξ
      = diag θA θB ρ ξ * qHat θA θB πA πB ξ + twoQ1 θA θB πA πB ξ :=
  source_identity_gen ξ (rising_ne_zero hθA _) (rising_ne_zero hθB _)

end Rhone.Probability.Denominator
