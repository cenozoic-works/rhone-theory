/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Obs
public import Rhone.LinearAlgebra.Recursion.Finite

/-! # Exact rescaled recursion for the parent-independent-mutation sampling probability -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F] {x : F}

def resc (x : F) (q : Config KA KB → F) (ξ : Config KA KB) : F := (x ^ obsTot ξ)⁻¹ * q ξ

def errA (h : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ i, (if ξ.mA i = 1 then 0 else
    (((ξ.a i : ℕ) : F) * h (ξ.dropA i) + ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.killA i j)))

def errB (h : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ j, (if ξ.mB j = 1 then 0 else
    (((ξ.b j : ℕ) : F) * h (ξ.dropB j) + ∑ i, ((ξ.c i j : ℕ) : F) * h (ξ.killB i j)))

theorem resc_mul (hx : x ≠ 0) (q : Config KA KB → F) (η : Config KA KB) :
    x ^ obsTot η * resc x q η = q η := by
  rw [resc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]

theorem term_eq (hx : x ≠ 0) (q : Config KA KB → F) (w : F) (ξ η : Config KA KB)
    (h : w ≠ 0 → obsTot η = obsTot ξ) :
    (x ^ obsTot ξ)⁻¹ * (w * q η) = w * resc x q η := by
  by_cases hw : w = 0
  · simp [hw]
  · have hp : (x ^ obsTot ξ)⁻¹ * x ^ obsTot η = 1 := by
      rw [h hw, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    calc (x ^ obsTot ξ)⁻¹ * (w * q η)
        = ((x ^ obsTot ξ)⁻¹ * x ^ obsTot η) * (w * resc x q η) := by
          rw [← resc_mul hx q η]; ring
      _ = w * resc x q η := by rw [hp, one_mul]

theorem term_eq_inv (hx : x ≠ 0) (q : Config KA KB → F) (w : F) (ξ η : Config KA KB)
    (h : w ≠ 0 → obsTot η + 1 = obsTot ξ) :
    (x ^ obsTot ξ)⁻¹ * (w * q η) = x⁻¹ * (w * resc x q η) := by
  by_cases hw : w = 0
  · simp [hw]
  · have hp : (x ^ obsTot ξ)⁻¹ * x ^ obsTot η = x⁻¹ := by
      rw [← h hw, pow_succ]
      field_simp
    calc (x ^ obsTot ξ)⁻¹ * (w * q η)
        = ((x ^ obsTot ξ)⁻¹ * x ^ obsTot η) * (w * resc x q η) := by
          rw [← resc_mul hx q η]; ring
      _ = x⁻¹ * (w * resc x q η) := by rw [hp]

section Lines

variable (q : Config KA KB → F) (ξ : Config KA KB)

theorem lineA (hx : x ≠ 0) (i : Fin KA) :
    (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
      = (((dropIndA ξ i : ℕ) : F) * resc x q (ξ.dropA i)
          + ∑ j, ((killIndA ξ i j : ℕ) : F) * resc x q (ξ.killA i j))
        + x * (if ξ.mA i = 1 then 0 else
            (((ξ.a i : ℕ) : F) * resc x q (ξ.dropA i)
              + ∑ j, ((ξ.c i j : ℕ) : F) * resc x q (ξ.killA i j))) := by
  have hexp : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
      = (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)))
        + ∑ j, (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j))) := by
    simp only [mul_add, Finset.mul_sum]
  have hmA : ξ.mA i = ξ.a i + ξ.cRow i := rfl
  by_cases hm : ξ.mA i = 1
  · have hdrop : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)))
        = ((dropIndA ξ i : ℕ) : F) * resc x q (ξ.dropA i) := by
      by_cases ha : ξ.a i = 0
      · rw [dropIndA_eq_zero_of ξ ha, ha]; simp
      · have ha1 : ξ.a i = 1 := by omega
        have hrow : ξ.cRow i = 0 := by omega
        have hd : dropIndA ξ i = 1 := by simp [dropIndA, ha1, hrow]
        have key := term_eq_inv hx q (((ξ.a i : ℕ) : F)) ξ (ξ.dropA i)
          (fun _ => obsTot_dropA_of_eq_one ξ ha hm)
        calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)))
            = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.a i : ℕ) : F) * q (ξ.dropA i))) := by ring
          _ = x * (x⁻¹ * (((ξ.a i : ℕ) : F) * resc x q (ξ.dropA i))) := by rw [key]
          _ = ((dropIndA ξ i : ℕ) : F) * resc x q (ξ.dropA i) := by
              rw [hd, ha1]; push_cast; field_simp
    have hkill : ∀ j : Fin KB,
        (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
          = ((killIndA ξ i j : ℕ) : F) * resc x q (ξ.killA i j) := by
      intro j
      by_cases hc : ξ.c i j = 0
      · rw [killIndA_eq_zero_of ξ hc, hc]; simp
      · have hle := ξ.le_cRow i j
        have hc1 : ξ.c i j = 1 := by omega
        have hk : killIndA ξ i j = 1 := by simp [killIndA, hm, hc1]
        have key := term_eq_inv hx q (((ξ.c i j : ℕ) : F)) ξ (ξ.killA i j)
          (fun _ => obsTot_killA_of_eq_one ξ hc hm)
        calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
            = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j))) := by ring
          _ = x * (x⁻¹ * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killA i j))) := by rw [key]
          _ = ((killIndA ξ i j : ℕ) : F) * resc x q (ξ.killA i j) := by
              rw [hk, hc1]; push_cast; field_simp
    rw [hexp, hdrop, Finset.sum_congr rfl fun j _ => hkill j, hm]
    simp
  · have hd : dropIndA ξ i = 0 := by
      by_contra hne
      exact hm (mA_eq_one_of_dropIndA ξ hne)
    have hk : ∀ j : Fin KB, killIndA ξ i j = 0 := by
      intro j
      by_contra hne
      exact hm (mA_eq_one_of_killIndA ξ hne)
    have hdrop : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)))
        = x * (((ξ.a i : ℕ) : F) * resc x q (ξ.dropA i)) := by
      have key := term_eq hx q (((ξ.a i : ℕ) : F)) ξ (ξ.dropA i) (fun hw => by
        have ha : ξ.a i ≠ 0 := fun h0 => hw (by rw [h0]; simp)
        exact obsTot_dropA_of_two_le ξ ha (by omega))
      calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)))
          = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.a i : ℕ) : F) * q (ξ.dropA i))) := by ring
        _ = x * (((ξ.a i : ℕ) : F) * resc x q (ξ.dropA i)) := by rw [key]
    have hkill : ∀ j : Fin KB,
        (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
          = x * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killA i j)) := by
      intro j
      have hle := ξ.le_cRow i j
      have key := term_eq hx q (((ξ.c i j : ℕ) : F)) ξ (ξ.killA i j) (fun hw => by
        have hc : ξ.c i j ≠ 0 := fun h0 => hw (by rw [h0]; simp)
        exact obsTot_killA_of_two_le ξ hc (by omega))
      calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
          = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.c i j : ℕ) : F) * q (ξ.killA i j))) := by ring
        _ = x * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killA i j)) := by rw [key]
    rw [hexp, hdrop, Finset.sum_congr rfl fun j _ => hkill j, ite_eq_right hm, hd]
    simp only [hk, Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
    ring

theorem lineB (hx : x ≠ 0) (j : Fin KB) :
    (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
      = (((dropIndB ξ j : ℕ) : F) * resc x q (ξ.dropB j)
          + ∑ i, ((killIndB ξ i j : ℕ) : F) * resc x q (ξ.killB i j))
        + x * (if ξ.mB j = 1 then 0 else
            (((ξ.b j : ℕ) : F) * resc x q (ξ.dropB j)
              + ∑ i, ((ξ.c i j : ℕ) : F) * resc x q (ξ.killB i j))) := by
  have hexp : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
      = (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)))
        + ∑ i, (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j))) := by
    simp only [mul_add, Finset.mul_sum]
  have hmB : ξ.mB j = ξ.b j + ξ.cCol j := rfl
  by_cases hm : ξ.mB j = 1
  · have hdrop : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)))
        = ((dropIndB ξ j : ℕ) : F) * resc x q (ξ.dropB j) := by
      by_cases hb : ξ.b j = 0
      · rw [dropIndB_eq_zero_of ξ hb, hb]; simp
      · have hb1 : ξ.b j = 1 := by omega
        have hcol : ξ.cCol j = 0 := by omega
        have hd : dropIndB ξ j = 1 := by simp [dropIndB, hb1, hcol]
        have key := term_eq_inv hx q (((ξ.b j : ℕ) : F)) ξ (ξ.dropB j)
          (fun _ => obsTot_dropB_of_eq_one ξ hb hm)
        calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)))
            = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.b j : ℕ) : F) * q (ξ.dropB j))) := by ring
          _ = x * (x⁻¹ * (((ξ.b j : ℕ) : F) * resc x q (ξ.dropB j))) := by rw [key]
          _ = ((dropIndB ξ j : ℕ) : F) * resc x q (ξ.dropB j) := by
              rw [hd, hb1]; push_cast; field_simp
    have hkill : ∀ i : Fin KA,
        (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
          = ((killIndB ξ i j : ℕ) : F) * resc x q (ξ.killB i j) := by
      intro i
      by_cases hc : ξ.c i j = 0
      · rw [killIndB_eq_zero_of ξ hc, hc]; simp
      · have hle := ξ.le_cCol i j
        have hc1 : ξ.c i j = 1 := by omega
        have hk : killIndB ξ i j = 1 := by simp [killIndB, hm, hc1]
        have key := term_eq_inv hx q (((ξ.c i j : ℕ) : F)) ξ (ξ.killB i j)
          (fun _ => obsTot_killB_of_eq_one ξ hc hm)
        calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
            = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j))) := by ring
          _ = x * (x⁻¹ * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killB i j))) := by rw [key]
          _ = ((killIndB ξ i j : ℕ) : F) * resc x q (ξ.killB i j) := by
              rw [hk, hc1]; push_cast; field_simp
    rw [hexp, hdrop, Finset.sum_congr rfl fun i _ => hkill i, hm]
    simp
  · have hd : dropIndB ξ j = 0 := by
      by_contra hne
      exact hm (mB_eq_one_of_dropIndB ξ hne)
    have hk : ∀ i : Fin KA, killIndB ξ i j = 0 := by
      intro i
      by_contra hne
      exact hm (mB_eq_one_of_killIndB ξ hne)
    have hdrop : (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)))
        = x * (((ξ.b j : ℕ) : F) * resc x q (ξ.dropB j)) := by
      have key := term_eq hx q (((ξ.b j : ℕ) : F)) ξ (ξ.dropB j) (fun hw => by
        have hb : ξ.b j ≠ 0 := fun h0 => hw (by rw [h0]; simp)
        exact obsTot_dropB_of_two_le ξ hb (by omega))
      calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)))
          = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.b j : ℕ) : F) * q (ξ.dropB j))) := by ring
        _ = x * (((ξ.b j : ℕ) : F) * resc x q (ξ.dropB j)) := by rw [key]
    have hkill : ∀ i : Fin KA,
        (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
          = x * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killB i j)) := by
      intro i
      have hle := ξ.le_cCol i j
      have key := term_eq hx q (((ξ.c i j : ℕ) : F)) ξ (ξ.killB i j) (fun hw => by
        have hc : ξ.c i j ≠ 0 := fun h0 => hw (by rw [h0]; simp)
        exact obsTot_killB_of_two_le ξ hc (by omega))
      calc (x ^ obsTot ξ)⁻¹ * (x * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
          = x * ((x ^ obsTot ξ)⁻¹ * (((ξ.c i j : ℕ) : F) * q (ξ.killB i j))) := by ring
        _ = x * (((ξ.c i j : ℕ) : F) * resc x q (ξ.killB i j)) := by rw [key]
    rw [hexp, hdrop, Finset.sum_congr rfl fun i _ => hkill i, ite_eq_right hm, hd]
    simp only [hk, Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
    ring

end Lines

theorem rescaled_rhs (hx : x ≠ 0) (θA θB ρ : F) (q : Config KA KB → F) (ξ : Config KA KB) :
    (x ^ obsTot ξ)⁻¹ * rhs θA θB ρ (fun _ => x) (fun _ => x) q ξ
      = rhsIA θA θB ρ (resc x q) ξ
        + x * (θA * errA (resc x q) ξ + θB * errB (resc x q) ξ) := by
  have e1 : (x ^ obsTot ξ)⁻¹ * (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
      = ∑ i, ((ξ.coalA i : ℕ) : F) * resc x q (ξ.dropA i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => term_eq hx q _ ξ _ fun hw => ?_
    have h0 : ξ.coalA i ≠ 0 := fun hz => hw (by rw [hz]; simp)
    have ha : ξ.a i ≠ 0 := fun hz => h0 (ξ.coalA_eq_zero_of hz)
    exact obsTot_dropA_of_two_le ξ ha (two_le_mA_of_coalA ξ h0)
  have e2 : (x ^ obsTot ξ)⁻¹ * (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
      = ∑ j, ((ξ.coalB j : ℕ) : F) * resc x q (ξ.dropB j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => term_eq hx q _ ξ _ fun hw => ?_
    have h0 : ξ.coalB j ≠ 0 := fun hz => hw (by rw [hz]; simp)
    have hb : ξ.b j ≠ 0 := fun hz => h0 (ξ.coalB_eq_zero_of hz)
    exact obsTot_dropB_of_two_le ξ hb (two_le_mB_of_coalB ξ h0)
  have e3 : (x ^ obsTot ξ)⁻¹ * (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
      = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * resc x q (ξ.dropC i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => term_eq hx q _ ξ _ fun hw => ?_
    have h0 : ξ.coalC i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
    exact obsTot_dropC ξ h0
  have e4 : (x ^ obsTot ξ)⁻¹ * (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
      = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * resc x q (ξ.mergeAB i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => term_eq hx q _ ξ _ fun hw => ?_
    have h0 : ξ.coalAB i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
    have ha : ξ.a i ≠ 0 := fun hz => h0 (ξ.coalAB_eq_zero_left j hz)
    have hb : ξ.b j ≠ 0 := fun hz => h0 (ξ.coalAB_eq_zero_right i hz)
    exact obsTot_mergeAB ξ ha hb
  have e7 : (x ^ obsTot ξ)⁻¹ * (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j))
      = ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * resc x q (ξ.split i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => term_eq hx q _ ξ _ fun hw => ?_
    have h0 : ξ.c i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
    exact obsTot_split ξ h0
  have e5 : (x ^ obsTot ξ)⁻¹ * (∑ i, x * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
      = (∑ i, (((dropIndA ξ i : ℕ) : F) * resc x q (ξ.dropA i)
          + ∑ j, ((killIndA ξ i j : ℕ) : F) * resc x q (ξ.killA i j)))
        + x * errA (resc x q) ξ := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => lineA q ξ hx i,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have e6 : (x ^ obsTot ξ)⁻¹ * (∑ j, x * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
      = (∑ j, (((dropIndB ξ j : ℕ) : F) * resc x q (ξ.dropB j)
          + ∑ i, ((killIndB ξ i j : ℕ) : F) * resc x q (ξ.killB i j)))
        + x * errB (resc x q) ξ := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => lineB q ξ hx j,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  simp only [rhs, rhsIA]
  linear_combination e1 + e2 + e3 + e4 + ρ * e7 + θA * e5 + θB * e6

theorem rescaled_recursion (hx : x ≠ 0) {θA θB ρ : F} {q : Config KA KB → F}
    (h : IsSolution θA θB ρ (fun _ => x) (fun _ => x) q) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    diag θA θB ρ ξ * resc x q ξ
      = rhsIA θA θB ρ (resc x q) ξ
        + x * (θA * errA (resc x q) ξ + θB * errB (resc x q) ξ) := by
  rw [← rescaled_rhs hx θA θB ρ q ξ, ← h.recursion ξ hn, resc]
  ring

theorem resc_boundary (hx : x ≠ 0) {θA θB ρ : F} {q : Config KA KB → F}
    (h : IsSolution θA θB ρ (fun _ => x) (fun _ => x) q) (ζ : Config KA KB) (hn : ζ.n ≤ 1) :
    resc x q ζ = 1 := by
  rcases Nat.lt_or_ge ζ.n 1 with h0 | h0
  · have hz : ζ = 0 := ζ.eq_zero_of_n_eq_zero (by omega)
    subst hz
    simp [resc, h.empty]
  · rcases ζ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
    · rw [resc, obsTot_eA, h.bdryA]
      field_simp
    · rw [resc, obsTot_eB, h.bdryB]
      field_simp
    · rw [resc, obsTot_eC, h.bdryC]
      field_simp

end Rhone.Probability.InfiniteAlleles
