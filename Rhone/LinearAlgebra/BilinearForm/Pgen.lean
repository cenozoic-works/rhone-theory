/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Generic bilinear form on slot polynomials and two points that separate it -/

@[expose] public section

namespace Rhone.LinearAlgebra.BilinearForm

open Finset

variable {S : Type*} [CommRing S] {KA KB : ℕ}

def prodAll {K : ℕ} (d : Fin K → S) : S := ∏ k, d k

def prodErase {K : ℕ} (d : Fin K → S) (i : Fin K) : S := ∏ k ∈ Finset.univ.erase i, d k

def sfac {K : ℕ} (d : Fin K → S) : S := (∑ k, d k) + (K : S) - 1

def Pgen (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ) (wAB : Fin KA → Fin KB → ℕ)
    (dA : Fin KA → S) (dB : Fin KB → S) : S :=
  (w0 : S) * (prodAll dA * prodAll dB)
    - sfac dA * (∑ i, (wA i : S) * prodErase dA i) * prodAll dB
    - sfac dB * (∑ j, (wB j : S) * prodErase dB j) * prodAll dA
    + sfac dA * sfac dB * (∑ i, ∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))

variable {T : Type*} [CommRing T]

theorem map_Pgen (φ : S →+* T) (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ)
    (wAB : Fin KA → Fin KB → ℕ) (dA : Fin KA → S) (dB : Fin KB → S) :
    φ (Pgen w0 wA wB wAB dA dB)
      = Pgen w0 wA wB wAB (fun i => φ (dA i)) (fun j => φ (dB j)) := by
  simp only [Pgen, prodAll, prodErase, sfac, map_add, map_sub, map_mul, map_sum, map_prod,
    map_natCast, map_one]

theorem Pgen_of_key (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ)
    (wAB : Fin KA → Fin KB → ℕ) {dA : Fin KA → S} {dB : Fin KB → S}
    (hA : ∀ i, sfac dA * prodErase dA i = prodAll dA)
    (hB : ∀ j, sfac dB * prodErase dB j = prodAll dB) :
    Pgen w0 wA wB wAB dA dB
      = prodAll dA * prodAll dB
        * ((w0 : S) - (∑ i, (wA i : S)) - (∑ j, (wB j : S))
            + ∑ i, ∑ j, (wAB i j : S)) := by
  have e2 : sfac dA * (∑ i, (wA i : S) * prodErase dA i)
      = (∑ i, (wA i : S)) * prodAll dA := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [← hA i]; ring
  have e3 : sfac dB * (∑ j, (wB j : S) * prodErase dB j)
      = (∑ j, (wB j : S)) * prodAll dB := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [← hB j]; ring
  have e4 : sfac dA * sfac dB
        * (∑ i, ∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))
      = (∑ i, ∑ j, (wAB i j : S)) * (prodAll dA * prodAll dB) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hA i, ← hB j]; ring
  rw [Pgen, e2, e3, e4]
  ring

theorem Pgen_of_pt_left (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ)
    (wAB : Fin KA → Fin KB → ℕ) {dA : Fin KA → S} {dB : Fin KB → S} (i₀ : Fin KA)
    (h0 : prodAll dA = 0) (h1 : prodErase dA i₀ = 1)
    (hz : ∀ i, i ≠ i₀ → prodErase dA i = 0)
    (hB : ∀ j, sfac dB * prodErase dB j = prodAll dB) :
    Pgen w0 wA wB wAB dA dB
      = -(sfac dA * prodAll dB * ((wA i₀ : S) - ∑ j, (wAB i₀ j : S))) := by
  have e2 : (∑ i, (wA i : S) * prodErase dA i) = (wA i₀ : S) := by
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
    · rw [h1, mul_one]
    · intro i _ hi; rw [hz i hi, mul_zero]
  have e4 : sfac dA * sfac dB
        * (∑ i, ∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))
      = sfac dA * prodAll dB * ∑ j, (wAB i₀ j : S) := by
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h1, ← hB j]; ring
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hz i hi, zero_mul, mul_zero]
  rw [Pgen, e2, e4, h0]
  ring

theorem Pgen_of_pt_right (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ)
    (wAB : Fin KA → Fin KB → ℕ) {dA : Fin KA → S} {dB : Fin KB → S} (j₀ : Fin KB)
    (hA : ∀ i, sfac dA * prodErase dA i = prodAll dA)
    (h0 : prodAll dB = 0) (h1 : prodErase dB j₀ = 1)
    (hz : ∀ j, j ≠ j₀ → prodErase dB j = 0) :
    Pgen w0 wA wB wAB dA dB
      = -(sfac dB * prodAll dA * ((wB j₀ : S) - ∑ i, (wAB i j₀ : S))) := by
  have e3 : (∑ j, (wB j : S) * prodErase dB j) = (wB j₀ : S) := by
    rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ j₀)]
    · rw [h1, mul_one]
    · intro j _ hj; rw [hz j hj, mul_zero]
  have e4 : sfac dA * sfac dB
        * (∑ i, ∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))
      = sfac dB * prodAll dA * ∑ i, (wAB i j₀ : S) := by
    have hinner : ∀ i : Fin KA,
        (∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))
          = (wAB i j₀ : S) * prodErase dA i := by
      intro i
      rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ j₀)]
      · rw [h1, mul_one]
      · intro j _ hj; rw [hz j hj, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA i]; ring
  rw [Pgen, e3, e4, h0]
  ring

theorem Pgen_of_pt_both (w0 : ℕ) (wA : Fin KA → ℕ) (wB : Fin KB → ℕ)
    (wAB : Fin KA → Fin KB → ℕ) {dA : Fin KA → S} {dB : Fin KB → S}
    (i₀ : Fin KA) (j₀ : Fin KB)
    (hA0 : prodAll dA = 0) (hA1 : prodErase dA i₀ = 1)
    (hAz : ∀ i, i ≠ i₀ → prodErase dA i = 0)
    (hB0 : prodAll dB = 0) (hB1 : prodErase dB j₀ = 1)
    (hBz : ∀ j, j ≠ j₀ → prodErase dB j = 0) :
    Pgen w0 wA wB wAB dA dB = sfac dA * sfac dB * (wAB i₀ j₀ : S) := by
  have e4 : (∑ i, ∑ j, (wAB i j : S) * (prodErase dA i * prodErase dB j))
      = (wAB i₀ j₀ : S) := by
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
    · rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ j₀)]
      · rw [hA1, hB1, mul_one, mul_one]
      · intro j _ hj; rw [hBz j hj, mul_zero, mul_zero]
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hAz i hi, zero_mul, mul_zero]
  rw [Pgen, e4, hA0, hB0]
  ring

def ptNeg (K : ℕ) : Fin K → S := fun _ => -1

def ptOne {K : ℕ} (i₀ : Fin K) : Fin K → S := fun k => if k = i₀ then 0 else 1

theorem fin_pos {K : ℕ} (i : Fin K) : 0 < K := Fin.pos i

@[simp] theorem prodAll_ptNeg (K : ℕ) : prodAll (ptNeg K : Fin K → S) = (-1) ^ K := by
  simp [prodAll, ptNeg]

@[simp] theorem prodErase_ptNeg {K : ℕ} (i : Fin K) :
    prodErase (ptNeg K : Fin K → S) i = (-1) ^ (K - 1) := by
  simp [prodErase, ptNeg, Finset.card_erase_of_mem]

@[simp] theorem sfac_ptNeg (K : ℕ) : sfac (ptNeg K : Fin K → S) = -1 := by
  simp only [sfac, ptNeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_neg, mul_one]
  ring

theorem key_ptNeg {K : ℕ} (i : Fin K) :
    sfac (ptNeg K : Fin K → S) * prodErase (ptNeg K : Fin K → S) i
      = prodAll (ptNeg K : Fin K → S) := by
  have hK : 0 < K := fin_pos i
  rw [sfac_ptNeg, prodErase_ptNeg, prodAll_ptNeg, ← pow_succ']
  congr 1
  omega

@[simp] theorem prodAll_ptOne {K : ℕ} (i₀ : Fin K) : prodAll (ptOne i₀ : Fin K → S) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [ptOne])

@[simp] theorem prodErase_ptOne_self {K : ℕ} (i₀ : Fin K) :
    prodErase (ptOne i₀ : Fin K → S) i₀ = 1 :=
  Finset.prod_eq_one fun k hk => by simp [ptOne, (Finset.mem_erase.mp hk).1]

theorem prodErase_ptOne_of_ne {K : ℕ} {i₀ i : Fin K} (h : i ≠ i₀) :
    prodErase (ptOne i₀ : Fin K → S) i = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ i₀⟩) (by simp [ptOne])

theorem sfac_ptOne {K : ℕ} (i₀ : Fin K) :
    sfac (ptOne i₀ : Fin K → S) = 2 * (K : S) - 2 := by
  have hK : 0 < K := fin_pos i₀
  have h1 : ∀ k ∈ Finset.univ.erase i₀, (ptOne i₀ : Fin K → S) k = 1 := by
    intro k hk
    simp [ptOne, (Finset.mem_erase.mp hk).1]
  have hsum : (∑ k, (ptOne i₀ : Fin K → S) k) = ((K - 1 : ℕ) : S) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), Finset.sum_congr rfl h1,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀)]
    simp [ptOne]
  have hK1 : 1 ≤ K := hK
  have hcast : ((K - 1 : ℕ) : S) = (K : S) - 1 := by
    rw [Nat.cast_sub hK1, Nat.cast_one]
  rw [sfac, hsum, hcast]
  ring

end Rhone.LinearAlgebra.BilinearForm
