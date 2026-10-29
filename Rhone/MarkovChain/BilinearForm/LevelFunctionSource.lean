/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BilinearForm.Counting
public import Rhone.MarkovChain.ClosedForms.TwoSampleKappa

/-! # The block-`(2,2)` source is a level function -/

@[expose] public section

namespace Rhone.MarkovChain.BilinearForm

open Finset LinearAlgebra.Recursion Config ClosedForms Probability.Denominator

theorem two_mul_choose_two : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1)
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    have ih : 2 * (k + 1).choose 2 = (k + 1) * k := two_mul_choose_two (k + 1)
    have h : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [h, Nat.mul_add, ih]
    change 2 * (k + 1) + (k + 1) * k = (k + 2) * (k + 1)
    ring

variable {K KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ θA θB : F} {π : Fin K → F} {πA : Fin KA → F} {πB : Fin KB → F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem sum_mulPred_qOne_eq (m : Fin K → ℕ) :
    ∑ i, ((m i * (m i - 1) : ℕ) : F) * qOne θ π (decf m i)
      = 2 * (qOne θ π m - Gval θ π m) := by
  have hcast : ∀ i : Fin K,
      ((m i * (m i - 1) : ℕ) : F) = 2 * ((Nat.choose (m i) 2 : ℕ) : F) := by
    intro i
    rw [← two_mul_choose_two (m i)]
    push_cast
    ring
  rw [Gval]
  have hsimp : qOne θ π m
      - (qOne θ π m - ∑ i, ((Nat.choose (m i) 2 : ℕ) : F) * qOne θ π (decf m i))
      = ∑ i, ((Nat.choose (m i) 2 : ℕ) : F) * qOne θ π (decf m i) := by ring
  rw [hsimp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hcast i]; ring

theorem twoQ1_eq_of_t_two {ξ : Config KA KB} (ht : ξ.t = 2) (ha : ξ.sumA = 0)
    (hb : ξ.sumB = 0) :
    twoQ1 θA θB πA πB ξ = 2 * (Gval θA πA ξ.mA * Gval θB πB ξ.mB) := by
  have hmA : ∀ i, ξ.mA i = ξ.cRow i := by
    intro i
    have hz := ξ.a_eq_zero_of_sumA ha
    simp [Config.mA, hz]
  have hmB : ∀ j, ξ.mB j = ξ.cCol j := by
    intro j
    have hz := ξ.b_eq_zero_of_sumB hb
    simp [Config.mB, hz]
  have hSA : (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i))
      = 2 * (qOne θA πA ξ.mA - Gval θA πA ξ.mA) := by
    rw [← sum_mulPred_qOne_eq (θ := θA) (π := πA) ξ.mA]
    exact Finset.sum_congr rfl fun i _ => by rw [hmA i]
  have hSB : (∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j))
      = 2 * (qOne θB πB ξ.mB - Gval θB πB ξ.mB) := by
    rw [← sum_mulPred_qOne_eq (θ := θB) (π := πB) ξ.mB]
    exact Finset.sum_congr rfl fun j _ => by rw [hmB j]
  have hT := Probability.BilinearForm.two_mul_sumC_eq ξ ht (fun i => qOne θA πA (decf ξ.mA i))
    (fun j => qOne θB πB (decf ξ.mB j))
  rw [hSA, hSB] at hT
  have htt : ((ξ.t * (ξ.t - 1) : ℕ) : F) = 2 := by rw [ht]; norm_num
  rw [twoQ1, htt, hSA, hSB]
  linear_combination hT / 2

theorem twoQ1_block22 {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    twoQ1 θA θB πA πB ξ
      = 2 * (if ξ.t = 2 then Gval θA πA ξ.mA * Gval θB πB ξ.mB else 0) := by
  rcases eq_or_ne ξ.t 2 with h | h
  · have ha : ξ.sumA = 0 := by simp only [Config.nA] at hA; omega
    have hb : ξ.sumB = 0 := by simp only [Config.nB] at hB; omega
    rw [ite_eq_left h, twoQ1_eq_of_t_two h ha hb]
  · have ht1 : ξ.t ≤ 1 := by
      have := ξ.t_le_nA
      omega
    rw [ite_eq_right h, twoQ1_eq_zero_of_t_le_one ξ ht1]
    ring

end Rhone.MarkovChain.BilinearForm
