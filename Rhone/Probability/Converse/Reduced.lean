/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Converse.Defs
public import Rhone.Probability.RecombinationExpansion.Kernel

/-! # The reduced `t = 0` recursion for the ratio of `q` to its product form -/

@[expose] public section

namespace Rhone.Probability.Converse

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion
    RecombinationExpansion
open Analysis.RecombinationExpansion RecombinationExpansion

variable {KA KB : ℕ}

def cfg0 (a : Fin KA → ℕ) (b : Fin KB → ℕ) : Config KA KB := ⟨a, b, fun _ _ => 0⟩

@[simp] theorem cfg0_a (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).a = a := rfl

@[simp] theorem cfg0_b (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).b = b := rfl

@[simp] theorem cfg0_t (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).t = 0 := by
  simp [cfg0, Config.t]

@[simp] theorem cfg0_nA (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).nA = ∑ i, a i := by
  simp [Config.nA, Config.sumA, cfg0_t]

@[simp] theorem cfg0_nB (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).nB = ∑ j, b j := by
  simp [Config.nB, Config.sumB, cfg0_t]

@[simp] theorem cfg0_dropA (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i : Fin KA) :
    (cfg0 a b).dropA i = cfg0 (decf a i) b := rfl

@[simp] theorem cfg0_dropB (a : Fin KA → ℕ) (b : Fin KB → ℕ) (j : Fin KB) :
    (cfg0 a b).dropB j = cfg0 a (decf b j) := rfl

@[simp] theorem cfg0_coalAB (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    (cfg0 a b).coalAB i j = 2 * (a i * b j) := rfl

section Positivity

variable {K : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem qOne_pos {θ : F} {π : Fin K → F} (hθ : 0 < θ) (hπ : ∀ i, 0 < π i) (m : Fin K → ℕ) :
    0 < qOne θ π m :=
  div_pos (Finset.prod_pos fun i _ => rising_pos (mul_pos hθ (hπ i)) _) (rising_pos hθ _)

theorem qOne_ne_zero {θ : F} {π : Fin K → F} (hθ : 0 < θ) (hπ : ∀ i, 0 < π i) (m : Fin K → ℕ) :
    qOne θ π m ≠ 0 := (qOne_pos hθ hπ m).ne'

end Positivity

section Reduced

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

def gVal (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (q2 : Config KA KB → F)
    (a : Fin KA → ℕ) (b : Fin KB → ℕ) : F :=
  q2 (cfg0 a b) / (qOne θA πA a * qOne θB πB b)

theorem downA_term (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB) (hπB : ∀ j, 0 < πB j)
    (q2 : Config KA KB → F) (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i : Fin KA) :
    (((a i * (a i - 1) : ℕ) : F) + θA * πA i * ((a i : ℕ) : F)) * q2 (cfg0 (decf a i) b)
      = (qOne θA πA a * qOne θB πB b)
        * (uu θA (∑ k, a k) * (((a i : ℕ) : F) * gVal θA θB πA πB q2 (decf a i) b)) := by
  by_cases h0 : a i = 0
  · rw [h0]
    simp
  · have hstep := qOne_step (θ := θA) (π := πA) hθA a i
    have hdec : qOne θA πA (decf a i) ≠ 0 := qOne_ne_zero hθA hπA _
    have hb : qOne θB πB b ≠ 0 := qOne_ne_zero hθB hπB _
    have hcoef : (((a i * (a i - 1) : ℕ) : F) + θA * πA i * ((a i : ℕ) : F))
        = ((a i : ℕ) : F) * (θA * πA i + ((a i : ℕ) : F) - 1) := by
      rw [natCast_mul_pred]
      ring
    rw [hcoef, gVal, uu]
    simp only [← mul_div_assoc]
    rw [eq_div_iff (mul_ne_zero hdec hb)]
    linear_combination q2 (cfg0 (decf a i) b) * qOne θB πB b * hstep

theorem downB_term (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB) (hπB : ∀ j, 0 < πB j)
    (q2 : Config KA KB → F) (a : Fin KA → ℕ) (b : Fin KB → ℕ) (j : Fin KB) :
    (((b j * (b j - 1) : ℕ) : F) + θB * πB j * ((b j : ℕ) : F)) * q2 (cfg0 a (decf b j))
      = (qOne θA πA a * qOne θB πB b)
        * (uu θB (∑ l, b l) * (((b j : ℕ) : F) * gVal θA θB πA πB q2 a (decf b j))) := by
  by_cases h0 : b j = 0
  · rw [h0]
    simp
  · have hstep := qOne_step (θ := θB) (π := πB) hθB b j
    have hdec : qOne θB πB (decf b j) ≠ 0 := qOne_ne_zero hθB hπB _
    have ha : qOne θA πA a ≠ 0 := qOne_ne_zero hθA hπA _
    have hcoef : (((b j * (b j - 1) : ℕ) : F) + θB * πB j * ((b j : ℕ) : F))
        = ((b j : ℕ) : F) * (θB * πB j + ((b j : ℕ) : F) - 1) := by
      rw [natCast_mul_pred]
      ring
    rw [hcoef, gVal, uu]
    simp only [← mul_div_assoc]
    rw [eq_div_iff (mul_ne_zero ha hdec)]
    linear_combination q2 (cfg0 a (decf b j)) * qOne θA πA a * hstep

theorem source_term {q2 : Config KA KB → F} (a : Fin KA → ℕ) (b : Fin KB → ℕ)
    (hsig : ∀ i j, a i ≠ 0 → b j ≠ 0 →
      sigmaOf q2 ((cfg0 a b).mergeAB i j)
        = 2 * (qOne θA πA a * qOne θB πB b) * Gcoef θA πA a i * Gcoef θB πB b j) :
    (∑ i, ∑ j, (((cfg0 a b).coalAB i j : ℕ) : F) * sigmaOf q2 ((cfg0 a b).mergeAB i j))
      = (qOne θA πA a * qOne θB πB b) * (4 * Phi θA πA a * Phi θB πB b) := by
  have hPhiA : Phi θA πA a = ∑ i, ((a i : ℕ) : F) * Gcoef θA πA a i := rfl
  have hPhiB : Phi θB πB b = ∑ j, ((b j : ℕ) : F) * Gcoef θB πB b j := rfl
  have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
      (((cfg0 a b).coalAB i j : ℕ) : F) * sigmaOf q2 ((cfg0 a b).mergeAB i j)
        = 4 * (qOne θA πA a * qOne θB πB b)
            * ((((a i : ℕ) : F) * Gcoef θA πA a i) * (((b j : ℕ) : F) * Gcoef θB πB b j)) := by
    intro i j
    by_cases ha : a i = 0
    · rw [cfg0_coalAB, ha]
      simp
    by_cases hb : b j = 0
    · rw [cfg0_coalAB, hb]
      simp
    · rw [hsig i j ha hb, cfg0_coalAB]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  have hin : ∀ i : Fin KA,
      (∑ j, 4 * (qOne θA πA a * qOne θB πB b)
          * ((((a i : ℕ) : F) * Gcoef θA πA a i) * (((b j : ℕ) : F) * Gcoef θB πB b j)))
        = (4 * (qOne θA πA a * qOne θB πB b) * Phi θB πB b) * (((a i : ℕ) : F)
            * Gcoef θA πA a i) := by
    intro i
    rw [hPhiB, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hin i, ← Finset.mul_sum, ← hPhiA]
  ring

theorem gRec (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB) (hπB : ∀ j, 0 < πB j)
    {q2 : Config KA KB → F} (a : Fin KA → ℕ) (b : Fin KB → ℕ)
    (hL0 : L0 θA θB πA πB q2 (cfg0 a b) = 0)
    (hsig : ∀ i j, a i ≠ 0 → b j ≠ 0 →
      sigmaOf q2 ((cfg0 a b).mergeAB i j)
        = 2 * (qOne θA πA a * qOne θB πB b) * Gcoef θA πA a i * Gcoef θB πB b j) :
    (((∑ i, a i : ℕ) : F) * uu θA (∑ i, a i) + ((∑ j, b j : ℕ) : F) * uu θB (∑ j, b j))
        * gVal θA θB πA πB q2 a b
      = uu θA (∑ i, a i) * ∑ i, ((a i : ℕ) : F) * gVal θA θB πA πB q2 (decf a i) b
        + uu θB (∑ j, b j) * ∑ j, ((b j : ℕ) : F) * gVal θA θB πA πB q2 a (decf b j)
        + 4 * Phi θA πA a * Phi θB πB b := by
  have hP : qOne θA πA a * qOne θB πB b ≠ 0 :=
    mul_ne_zero (qOne_ne_zero hθA hπA _) (qOne_ne_zero hθB hπB _)
  have hres := residual_t_zero_sigma (θA := θA) (θB := θB) (πA := πA) (πB := πB) (q2 := q2)
    (cfg0 a b) (cfg0_t a b) hL0
  simp only [cfg0_nA, cfg0_nB, cfg0_a, cfg0_b] at hres
  have hA : (∑ i, (((a i * (a i - 1) : ℕ) : F) + θA * πA i * ((a i : ℕ) : F))
        * q2 ((cfg0 a b).dropA i))
      = (qOne θA πA a * qOne θB πB b)
        * (uu θA (∑ k, a k) * ∑ i, ((a i : ℕ) : F) * gVal θA θB πA πB q2 (decf a i) b) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [cfg0_dropA]
      exact downA_term hθA hπA hθB hπB q2 a b i
  have hB : (∑ j, (((b j * (b j - 1) : ℕ) : F) + θB * πB j * ((b j : ℕ) : F))
        * q2 ((cfg0 a b).dropB j))
      = (qOne θA πA a * qOne θB πB b)
        * (uu θB (∑ l, b l) * ∑ j, ((b j : ℕ) : F) * gVal θA θB πA πB q2 a (decf b j)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [cfg0_dropB]
      exact downB_term hθA hπA hθB hπB q2 a b j
  rw [hA, hB, source_term a b hsig] at hres
  have hdiag : ((((∑ i, a i) * ((∑ i, a i) - 1) : ℕ)) : F) + θA * ((∑ i, a i : ℕ) : F)
      + ((((∑ j, b j) * ((∑ j, b j) - 1) : ℕ)) : F) + θB * ((∑ j, b j : ℕ) : F)
      = ((∑ i, a i : ℕ) : F) * uu θA (∑ i, a i)
        + ((∑ j, b j : ℕ) : F) * uu θB (∑ j, b j) := by
    rw [natCast_mul_pred, natCast_mul_pred, uu, uu]
    ring
  rw [hdiag] at hres
  rw [show gVal θA θB πA πB q2 a b
      = q2 (cfg0 a b) / (qOne θA πA a * qOne θB πB b) from rfl, ← mul_div_assoc,
    div_eq_iff hP]
  linear_combination hres

end Reduced

end Rhone.Probability.Converse
