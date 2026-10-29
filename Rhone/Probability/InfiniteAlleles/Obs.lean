/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Defs
public import Rhone.LinearAlgebra.Recursion.Block

/-! # The number of alleles *observed*, and how the seven moves change it -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

def obs {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) : ℕ :=
  (Finset.univ.filter fun i => f i ≠ 0).card

section Obs

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ} {i : ι}

theorem obs_decf_of_two_le (h : 2 ≤ f i) : obs (decf f i) = obs f := by
  have hset : (Finset.univ.filter fun k => decf f i k ≠ 0)
      = (Finset.univ.filter fun k => f k ≠ 0) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : k = i
    · subst hk; rw [decf_self]; omega
    · rw [decf_of_ne _ hk]
  simp only [obs, hset]

theorem obs_decf_of_eq_one (h : f i = 1) : obs (decf f i) + 1 = obs f := by
  have hset : (Finset.univ.filter fun k => decf f i k ≠ 0)
      = (Finset.univ.filter fun k => f k ≠ 0).erase i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hk : k = i
    · subst hk; rw [decf_self, h]; simp
    · rw [decf_of_ne _ hk]; simp [hk]
  have hmem : i ∈ Finset.univ.filter fun k => f k ≠ 0 := by simp [h]
  rw [obs, obs, hset, Finset.card_erase_add_one hmem]

end Obs

def obsA (ξ : Config KA KB) : ℕ := obs ξ.mA

def obsB (ξ : Config KA KB) : ℕ := obs ξ.mB

def obsTot (ξ : Config KA KB) : ℕ := obsA ξ + obsB ξ

@[simp] theorem obsTot_zero : obsTot (0 : Config KA KB) = 0 := by
  have hA : (0 : Config KA KB).mA = fun _ => 0 := by
    funext i; simp [Config.mA, Config.cRow]
  have hB : (0 : Config KA KB).mB = fun _ => 0 := by
    funext j; simp [Config.mB, Config.cCol]
  simp [obsTot, obsA, obsB, obs, hA, hB]

theorem mA_eA (i i' : Fin KA) :
    (Config.eA i : Config KA KB).mA i' = if i' = i then 1 else 0 := by
  simp only [Config.mA, Config.cRow, Config.eA, Finset.sum_const_zero, Nat.add_zero]
  by_cases h : i' = i
  · subst h; simp [incf_self]
  · simp [incf_of_ne _ h, h]

theorem mB_eA (i : Fin KA) (j' : Fin KB) : (Config.eA i : Config KA KB).mB j' = 0 := by
  simp [Config.mB, Config.cCol, Config.eA]

theorem mB_eB (j j' : Fin KB) :
    (Config.eB j : Config KA KB).mB j' = if j' = j then 1 else 0 := by
  simp only [Config.mB, Config.cCol, Config.eB, Finset.sum_const_zero, Nat.add_zero]
  by_cases h : j' = j
  · subst h; simp [incf_self]
  · simp [incf_of_ne _ h, h]

theorem mA_eB (i' : Fin KA) (j : Fin KB) : (Config.eB j : Config KA KB).mA i' = 0 := by
  simp [Config.mA, Config.cRow, Config.eB]

theorem c_eC (i i' : Fin KA) (j j' : Fin KB) :
    (Config.eC i j : Config KA KB).c i' j' = if i' = i then (if j' = j then 1 else 0) else 0 := by
  by_cases h : i' = i
  · subst h
    simp only [Config.eC, incC, Function.update_self]
    by_cases hj : j' = j
    · subst hj; simp [incf_self]
    · simp [incf_of_ne _ hj, hj]
  · simp [Config.eC, incC, h]

theorem mA_eC (i i' : Fin KA) (j : Fin KB) :
    (Config.eC i j : Config KA KB).mA i' = if i' = i then 1 else 0 := by
  have ha : (Config.eC i j : Config KA KB).a i' = 0 := rfl
  simp only [Config.mA, Config.cRow, ha, Nat.zero_add]
  rw [Finset.sum_congr rfl fun j' _ => c_eC i i' j j']
  by_cases h : i' = i
  · subst h; simp
  · simp [h]

theorem mB_eC (i : Fin KA) (j j' : Fin KB) :
    (Config.eC i j : Config KA KB).mB j' = if j' = j then 1 else 0 := by
  have hb : (Config.eC i j : Config KA KB).b j' = 0 := rfl
  simp only [Config.mB, Config.cCol, hb, Nat.zero_add]
  rw [Finset.sum_congr rfl fun i' _ => c_eC i i' j j']
  by_cases h : j' = j
  · subst h; simp
  · simp [h]

theorem obs_eq_one_of_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    obs (fun k : ι => if k = i then 1 else 0) = 1 := by
  have hset : (Finset.univ.filter fun k : ι => (if k = i then 1 else 0) ≠ 0) = {i} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases h : k = i <;> simp [h]
  rw [obs, hset, Finset.card_singleton]

theorem obs_eq_zero_of_const_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    obs (fun _ : ι => 0) = 0 := by simp [obs]

@[simp] theorem obsTot_eA (i : Fin KA) : obsTot (Config.eA i : Config KA KB) = 1 := by
  have hA : (Config.eA i : Config KA KB).mA = fun k => if k = i then 1 else 0 :=
    funext fun i' => mA_eA i i'
  have hB : (Config.eA i : Config KA KB).mB = fun _ => 0 := funext fun j' => mB_eA i j'
  simp [obsTot, obsA, obsB, hA, hB, obs_eq_one_of_single, obs_eq_zero_of_const_zero]

@[simp] theorem obsTot_eB (j : Fin KB) : obsTot (Config.eB j : Config KA KB) = 1 := by
  have hA : (Config.eB j : Config KA KB).mA = fun _ => 0 := funext fun i' => mA_eB i' j
  have hB : (Config.eB j : Config KA KB).mB = fun k => if k = j then 1 else 0 :=
    funext fun j' => mB_eB j j'
  simp [obsTot, obsA, obsB, hA, hB, obs_eq_one_of_single, obs_eq_zero_of_const_zero]

@[simp] theorem obsTot_eC (i : Fin KA) (j : Fin KB) :
    obsTot (Config.eC i j : Config KA KB) = 2 := by
  have hA : (Config.eC i j : Config KA KB).mA = fun k => if k = i then 1 else 0 :=
    funext fun i' => mA_eC i i' j
  have hB : (Config.eC i j : Config KA KB).mB = fun k => if k = j then 1 else 0 :=
    funext fun j' => mB_eC i j j'
  simp [obsTot, obsA, obsB, hA, hB, obs_eq_one_of_single]

variable (ξ : Config KA KB) {i : Fin KA} {j : Fin KB}

theorem two_le_mA_of_coalA (h : ξ.coalA i ≠ 0) : 2 ≤ ξ.mA i := by
  simp only [Config.coalA, ne_eq, Nat.mul_eq_zero, not_or] at h
  have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
  omega

theorem two_le_mB_of_coalB (h : ξ.coalB j ≠ 0) : 2 ≤ ξ.mB j := by
  simp only [Config.coalB, ne_eq, Nat.mul_eq_zero, not_or] at h
  have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
  omega

theorem two_le_of_coalC (h : ξ.coalC i j ≠ 0) : 2 ≤ ξ.mA i ∧ 2 ≤ ξ.mB j := by
  simp only [Config.coalC, ne_eq, Nat.mul_eq_zero, not_or] at h
  have h1 := ξ.le_cRow i j
  have h2 := ξ.le_cCol i j
  have hmA : ξ.mA i = ξ.a i + ξ.cRow i := rfl
  have hmB : ξ.mB j = ξ.b j + ξ.cCol j := rfl
  omega

theorem obsTot_dropA_of_two_le (ha : ξ.a i ≠ 0) (h : 2 ≤ ξ.mA i) :
    obsTot (ξ.dropA i) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mA_dropA ha, ξ.mB_dropA i, obs_decf_of_two_le h]

theorem obsTot_dropA_of_eq_one (ha : ξ.a i ≠ 0) (h : ξ.mA i = 1) :
    obsTot (ξ.dropA i) + 1 = obsTot ξ := by
  have hd := obs_decf_of_eq_one (f := ξ.mA) (i := i) h
  simp only [obsTot, obsA, obsB, ξ.mA_dropA ha, ξ.mB_dropA i]
  omega

theorem obsTot_dropB_of_two_le (hb : ξ.b j ≠ 0) (h : 2 ≤ ξ.mB j) :
    obsTot (ξ.dropB j) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mB_dropB hb, ξ.mA_dropB j, obs_decf_of_two_le h]

theorem obsTot_dropC (h : ξ.coalC i j ≠ 0) : obsTot (ξ.dropC i j) = obsTot ξ := by
  obtain ⟨h1, h2⟩ := two_le_of_coalC ξ h
  have hc : ξ.c i j ≠ 0 := by
    simp only [Config.coalC, ne_eq, Nat.mul_eq_zero, not_or] at h; exact h.1
  simp only [obsTot, obsA, obsB, ξ.mA_dropC hc, ξ.mB_dropC hc,
    obs_decf_of_two_le h1, obs_decf_of_two_le h2]

theorem obsTot_mergeAB (ha : ξ.a i ≠ 0) (hb : ξ.b j ≠ 0) :
    obsTot (ξ.mergeAB i j) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mA_mergeAB j ha, ξ.mB_mergeAB i hb]

theorem obsTot_split (hc : ξ.c i j ≠ 0) : obsTot (ξ.split i j) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mA_split hc, ξ.mB_split hc]

theorem obsTot_killA_of_two_le (hc : ξ.c i j ≠ 0) (h : 2 ≤ ξ.mA i) :
    obsTot (ξ.killA i j) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mA_killA hc, ξ.mB_killA hc, obs_decf_of_two_le h]

theorem obsTot_killB_of_two_le (hc : ξ.c i j ≠ 0) (h : 2 ≤ ξ.mB j) :
    obsTot (ξ.killB i j) = obsTot ξ := by
  simp only [obsTot, obsA, obsB, ξ.mA_killB hc, ξ.mB_killB hc, obs_decf_of_two_le h]

theorem obsTot_dropB_of_eq_one (hb : ξ.b j ≠ 0) (h : ξ.mB j = 1) :
    obsTot (ξ.dropB j) + 1 = obsTot ξ := by
  have hd := obs_decf_of_eq_one (f := ξ.mB) (i := j) h
  simp only [obsTot, obsA, obsB, ξ.mB_dropB hb, ξ.mA_dropB j]
  omega

theorem obsTot_killA_of_eq_one (hc : ξ.c i j ≠ 0) (h : ξ.mA i = 1) :
    obsTot (ξ.killA i j) + 1 = obsTot ξ := by
  have hd := obs_decf_of_eq_one (f := ξ.mA) (i := i) h
  simp only [obsTot, obsA, obsB, ξ.mA_killA hc, ξ.mB_killA hc]
  omega

theorem obsTot_killB_of_eq_one (hc : ξ.c i j ≠ 0) (h : ξ.mB j = 1) :
    obsTot (ξ.killB i j) + 1 = obsTot ξ := by
  have hd := obs_decf_of_eq_one (f := ξ.mB) (i := j) h
  simp only [obsTot, obsA, obsB, ξ.mA_killB hc, ξ.mB_killB hc]
  omega

end Rhone.Probability.InfiniteAlleles
