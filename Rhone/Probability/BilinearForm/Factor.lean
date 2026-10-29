/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BilinearForm.Pgen
public import Rhone.Probability.BilinearForm.Counting

/-! # `q₁ = q_A q_B · uᵀMv`, with the denominators cleared -/

@[expose] public section

namespace Rhone.Probability.BilinearForm

open Finset LinearAlgebra.Recursion Config Denominator

variable {K KA KB : ℕ} {F : Type*} [Field F]
variable {θ θA θB : F} {π : Fin K → F} {πA : Fin KA → F} {πB : Fin KB → F}

def wt0 (ξ : Config KA KB) : ℕ := ξ.t * (ξ.t - 1)

def wtA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.cRow i * (ξ.cRow i - 1)

def wtB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.cCol j * (ξ.cCol j - 1)

def wtAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := ξ.c i j * (ξ.c i j - 1)

theorem wtA_eq_zero_of_mA (ξ : Config KA KB) {i : Fin KA} (h : ξ.mA i = 0) : wtA ξ i = 0 := by
  have hz : ξ.cRow i = 0 := by simp only [Config.mA] at h; omega
  simp [wtA, hz]

theorem wtAB_eq_zero_of_mA (ξ : Config KA KB) {i : Fin KA} (h : ξ.mA i = 0) (j : Fin KB) :
    wtAB ξ i j = 0 := by
  have hz : ξ.cRow i = 0 := by simp only [Config.mA] at h; omega
  have hc : ξ.c i j = 0 := by have := le_cRow ξ i j; omega
  simp [wtAB, hc]

theorem wtB_eq_zero_of_mB (ξ : Config KA KB) {j : Fin KB} (h : ξ.mB j = 0) : wtB ξ j = 0 := by
  have hz : ξ.cCol j = 0 := by simp only [Config.mB] at h; omega
  simp [wtB, hz]

theorem wtAB_eq_zero_of_mB (ξ : Config KA KB) {j : Fin KB} (h : ξ.mB j = 0) (i : Fin KA) :
    wtAB ξ i j = 0 := by
  have hz : ξ.cCol j = 0 := by simp only [Config.mB] at h; omega
  have hc : ξ.c i j = 0 := by have := le_cCol ξ i j; omega
  simp [wtAB, hc]

def dvalA (θA : F) (πA : Fin KA → F) (ξ : Config KA KB) (i : Fin KA) : F :=
  θA * πA i + ((ξ.mA i : ℕ) : F) - 1

def dvalB (θB : F) (πB : Fin KB → F) (ξ : Config KA KB) (j : Fin KB) : F :=
  θB * πB j + ((ξ.mB j : ℕ) : F) - 1

theorem sum_dvalA (hπA : ∑ i, πA i = 1) (ξ : Config KA KB) :
    (∑ i, dvalA θA πA ξ i) = θA + ((ξ.nA : ℕ) : F) - (KA : F) := by
  have hm : (∑ i, ((ξ.mA i : ℕ) : F)) = ((ξ.nA : ℕ) : F) := by
    rw [← Nat.cast_sum, ξ.sum_mA]
  simp only [dvalA, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hπA, hm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem sum_dvalB (hπB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    (∑ j, dvalB θB πB ξ j) = θB + ((ξ.nB : ℕ) : F) - (KB : F) := by
  have hm : (∑ j, ((ξ.mB j : ℕ) : F)) = ((ξ.nB : ℕ) : F) := by
    rw [← Nat.cast_sum, ξ.sum_mB]
  simp only [dvalB, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hπB, hm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem sfac_dvalA (hπA : ∑ i, πA i = 1) (ξ : Config KA KB) :
    LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) = θA + ((ξ.nA : ℕ) : F) - 1 := by
  rw [LinearAlgebra.BilinearForm.sfac, sum_dvalA hπA]
  ring

theorem sfac_dvalB (hπB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) = θB + ((ξ.nB : ℕ) : F) - 1 := by
  rw [LinearAlgebra.BilinearForm.sfac, sum_dvalB hπB]
  ring

theorem qOne_mul_prodAll (hπA : ∑ i, πA i = 1) (ξ : Config KA KB)
    (hden : rising θA ξ.nA ≠ 0) {i : Fin KA} (hi : ξ.mA i ≠ 0) :
    qOne θA πA (decf ξ.mA i) * LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ)
      = LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA *
          LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i := by
  have hsum : ∑ k, ξ.mA k = ξ.nA := ξ.sum_mA
  have hstep := qOne_step_of_ne_zero (θ := θA) (π := πA) ξ.mA hi (by rw [hsum]; exact hden)
  rw [hsum] at hstep
  have hprod : LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ) = dvalA θA πA ξ i *
      LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hprod, sfac_dvalA hπA]
  simp only [dvalA]
  linear_combination (LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i) * hstep

theorem qOne_mul_prodAll' (hπB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hden : rising θB ξ.nB ≠ 0) {j : Fin KB} (hj : ξ.mB j ≠ 0) :
    qOne θB πB (decf ξ.mB j) * LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ)
      = LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) * qOne θB πB ξ.mB *
          LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j := by
  have hsum : ∑ l, ξ.mB l = ξ.nB := ξ.sum_mB
  have hstep := qOne_step_of_ne_zero (θ := θB) (π := πB) ξ.mB hj (by rw [hsum]; exact hden)
  rw [hsum] at hstep
  have hprod : LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ) = dvalB θB πB ξ j *
      LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  rw [hprod, sfac_dvalB hπB]
  simp only [dvalB]
  linear_combination (LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j) * hstep

theorem twoQ1_mul_prodAll (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hdenA : rising θA ξ.nA ≠ 0) (hdenB : rising θB ξ.nB ≠ 0) :
    twoQ1 θA θB πA πB ξ *
        (LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ) * LinearAlgebra.BilinearForm.prodAll
        (dvalB θB πB ξ))
      = qOne θA πA ξ.mA * qOne θB πB ξ.mB
        * LinearAlgebra.BilinearForm.Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dvalA θA πA ξ)
            (dvalB θB πB ξ) := by
  have cA : ∀ (w : ℕ) (i : Fin KA), (ξ.mA i = 0 → w = 0) →
      (w : F) * (qOne θA πA (decf ξ.mA i) * LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ))
        = (w : F) * (LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA
            * LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i) := by
    intro w i hw
    by_cases h : ξ.mA i = 0
    · rw [hw h]; simp
    · rw [qOne_mul_prodAll hπA ξ hdenA h]
  have cB : ∀ (w : ℕ) (j : Fin KB), (ξ.mB j = 0 → w = 0) →
      (w : F) * (qOne θB πB (decf ξ.mB j) * LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ))
        = (w : F) * (LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) * qOne θB πB ξ.mB
            * LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j) := by
    intro w j hw
    by_cases h : ξ.mB j = 0
    · rw [hw h]; simp
    · rw [qOne_mul_prodAll' hπB ξ hdenB h]
  have hsA : (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i))
        * LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ)
      = LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA
        * ∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * LinearAlgebra.BilinearForm.prodErase
            (dvalA θA πA ξ) i := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination cA (ξ.cRow i * (ξ.cRow i - 1)) i fun h => wtA_eq_zero_of_mA ξ h
  have hsB : (∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j))
        * LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ)
      = LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) * qOne θB πB ξ.mB
        * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * LinearAlgebra.BilinearForm.prodErase
            (dvalB θB πB ξ) j := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination cB (ξ.cCol j * (ξ.cCol j - 1)) j fun h => wtB_eq_zero_of_mB ξ h
  have cAB : ∀ (i : Fin KA) (j : Fin KB),
      ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
          * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j))
          * (LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ) * LinearAlgebra.BilinearForm.prodAll
              (dvalB θB πB ξ))
        = ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
          * ((LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA)
              * (LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) * qOne θB πB ξ.mB))
          * (LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i *
              LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j) := by
    intro i j
    by_cases hA0 : ξ.mA i = 0
    · have : ξ.c i j * (ξ.c i j - 1) = 0 := wtAB_eq_zero_of_mA ξ hA0 j
      rw [this]; simp
    by_cases hB0 : ξ.mB j = 0
    · have : ξ.c i j * (ξ.c i j - 1) = 0 := wtAB_eq_zero_of_mB ξ hB0 i
      rw [this]; simp
    · have hA := qOne_mul_prodAll hπA ξ hdenA hA0
      have hB := qOne_mul_prodAll' hπB ξ hdenB hB0
      linear_combination
        (((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
            * (qOne θB πB (decf ξ.mB j) * LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ))) * hA
          + (((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
            * (LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA
              * LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i)) * hB
  have hsAB : (∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
          * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j)))
        * (LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ) * LinearAlgebra.BilinearForm.prodAll
            (dvalB θB πB ξ))
      = (LinearAlgebra.BilinearForm.sfac (dvalA θA πA ξ) * qOne θA πA ξ.mA)
          * (LinearAlgebra.BilinearForm.sfac (dvalB θB πB ξ) * qOne θB πB ξ.mB)
          * ∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
              * (LinearAlgebra.BilinearForm.prodErase (dvalA θA πA ξ) i *
                  LinearAlgebra.BilinearForm.prodErase (dvalB θB πB ξ) j) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination cAB i j
  simp only [twoQ1, LinearAlgebra.BilinearForm.Pgen, wt0, wtA, wtB, wtAB]
  linear_combination
    (-(qOne θB πB ξ.mB * LinearAlgebra.BilinearForm.prodAll (dvalB θB πB ξ))) * hsA
      + (-(qOne θA πA ξ.mA * LinearAlgebra.BilinearForm.prodAll (dvalA θA πA ξ))) * hsB + hsAB

end Rhone.Probability.BilinearForm
