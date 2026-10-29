/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs

/-! # `D(n_A, n_B)` and its divisibility bookkeeping -/

@[expose] public section

namespace Rhone.LinearAlgebra.SlotDeletion

open Finset

variable {R : Type*} [CommRing R]

def poch (θ : R) (n : ℕ) : R := ∏ k ∈ Finset.Ico 1 n, (θ + (k : R))

def Erect (a b r : R) (i j : ℕ) : R :=
  ∏ p ∈ Finset.Ico 2 (i + 1), ∏ s ∈ Finset.Ico 2 (j + 1), Tridiag.E R p s a b r

def Dfull (a b r : R) (i j : ℕ) : R := poch a i * poch b j * Erect a b r i j

def Dcut (a b r : R) (i j : ℕ) : R :=
  poch a i * poch b j
    * (Erect a b r (i - 1) j * ∏ s ∈ Finset.Ico 2 j, Tridiag.E R i s a b r)

@[simp] theorem poch_zero (θ : R) : poch θ 0 = 1 := by simp [poch]

@[simp] theorem poch_one (θ : R) : poch θ 1 = 1 := by simp [poch]

theorem poch_dvd (θ : R) {m n : ℕ} (h : m ≤ n) : poch θ m ∣ poch θ n :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Ico_subset_Ico le_rfl h)

theorem poch_succ_top (θ : R) {n : ℕ} (h : 2 ≤ n) :
    poch θ n = poch θ (n - 1) * (θ + ((n - 1 : ℕ) : R)) := by
  have key : poch θ ((n - 1) + 1) = poch θ (n - 1) * (θ + ((n - 1 : ℕ) : R)) := by
    rw [poch, Finset.prod_Ico_succ_top (by omega : 1 ≤ n - 1), ← poch]
  have h1 : (n - 1) + 1 = n := by omega
  rwa [h1] at key

@[simp] theorem Erect_zero_right (a b r : R) (i : ℕ) : Erect a b r i 0 = 1 := by
  simp [Erect]

@[simp] theorem Erect_zero_left (a b r : R) (j : ℕ) : Erect a b r 0 j = 1 := by
  simp [Erect]

@[simp] theorem Erect_one_right (a b r : R) (i : ℕ) : Erect a b r i 1 = 1 := by
  simp [Erect]

@[simp] theorem Erect_one_left (a b r : R) (j : ℕ) : Erect a b r 1 j = 1 := by
  simp [Erect]

theorem Dfull_j_zero (a b r : R) (i : ℕ) : Dfull a b r i 0 = poch a i := by
  simp [Dfull]

theorem Dfull_i_zero (a b r : R) (j : ℕ) : Dfull a b r 0 j = poch b j := by
  simp [Dfull]

theorem Erect_dvd_Erect (a b r : R) {i' j' i j : ℕ} (hi : i' ≤ i) (hj : j' ≤ j) :
    Erect a b r i' j' ∣ Erect a b r i j := by
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      Finset.prod_dvd_prod_of_subset _ _ _
        (Finset.Ico_subset_Ico le_rfl (by omega : j' + 1 ≤ j + 1))) ?_
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.Ico_subset_Ico le_rfl (by omega : i' + 1 ≤ i + 1))

theorem Erect_succ_row (a b r : R) {i : ℕ} (hi : 2 ≤ i) (j : ℕ) :
    Erect a b r i j = Erect a b r (i - 1) j * ∏ s ∈ Finset.Ico 2 (j + 1), Tridiag.E R i s a b r
    := by
  have h1 : i - 1 + 1 = i := by omega
  rw [Erect, Finset.prod_Ico_succ_top (by omega : 2 ≤ i), Erect, h1]

theorem prod_row_succ_top (a b r : R) (i : ℕ) {j : ℕ} (hj : 2 ≤ j) :
    (∏ s ∈ Finset.Ico 2 (j + 1), Tridiag.E R i s a b r)
      = (∏ s ∈ Finset.Ico 2 j, Tridiag.E R i s a b r) * Tridiag.E R i j a b r :=
  Finset.prod_Ico_succ_top (by omega) (fun s => Tridiag.E R i s a b r)

theorem Dcut_mul_E (a b r : R) {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    Dcut a b r i j * Tridiag.E R i j a b r = Dfull a b r i j := by
  rw [Dcut, Dfull, Erect_succ_row a b r hi j, prod_row_succ_top a b r i hj]
  ring

theorem Dfull_dvd_Dcut (a b r : R) {i' j' i j : ℕ} (hi' : i' ≤ i) (hj' : j' ≤ j)
    (hne : i' < i ∨ j' < j) (hi : 2 ≤ i) :
    Dfull a b r i' j' ∣ Dcut a b r i j := by
  refine mul_dvd_mul (mul_dvd_mul (poch_dvd a hi') (poch_dvd b hj')) ?_
  rcases Nat.lt_or_ge i' i with hlt | hge
  · exact Dvd.dvd.mul_right (Erect_dvd_Erect a b r (by omega) hj') _
  · have hi'' : i' = i := by omega
    have hjlt : j' < j := by rcases hne with h | h; exacts [absurd h (by omega), h]
    subst hi''
    rw [Erect_succ_row a b r hi j']
    refine mul_dvd_mul (Erect_dvd_Erect a b r le_rfl hj') ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _
      (Finset.Ico_subset_Ico le_rfl (by omega : j' + 1 ≤ j))

theorem Dfull_dvd_Dfull (a b r : R) {i' j' i j : ℕ} (hi : i' ≤ i) (hj : j' ≤ j) :
    Dfull a b r i' j' ∣ Dfull a b r i j :=
  mul_dvd_mul (mul_dvd_mul (poch_dvd a hi) (poch_dvd b hj)) (Erect_dvd_Erect a b r hi hj)

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem poch_map (θ : R) (n : ℕ) : f (poch θ n) = poch (f θ) n := by
  rw [poch, poch, map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [map_add, map_natCast]

theorem Erect_map (a b r : R) (i j : ℕ) : f (Erect a b r i j) = Erect (f a) (f b) (f r) i j := by
  rw [Erect, Erect, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun s _ => Tridiag.E_map f p s a b r

theorem Dfull_map (a b r : R) (i j : ℕ) :
    f (Dfull a b r i j) = Dfull (f a) (f b) (f r) i j := by
  rw [Dfull, Dfull, map_mul, map_mul, poch_map, poch_map, Erect_map]

theorem Dcut_map (a b r : R) (i j : ℕ) :
    f (Dcut a b r i j) = Dcut (f a) (f b) (f r) i j := by
  rw [Dcut, Dcut, map_mul, map_mul, map_mul, map_prod, poch_map, poch_map, Erect_map,
    Finset.prod_congr rfl fun s (_ : s ∈ Finset.Ico 2 j) => Tridiag.E_map f i s a b r]

end Map

end Rhone.LinearAlgebra.SlotDeletion
