/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Two-locus sample configurations and the elementary moves of the recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset

variable {KA KB : ℕ}

def incf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i + 1)

def decf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i - 1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem incf_self (f : ι → ℕ) (i : ι) : incf f i i = f i + 1 := by
  simp [incf]

omit [Fintype ι] in
theorem incf_of_ne (f : ι → ℕ) {i k : ι} (h : k ≠ i) : incf f i k = f k := by
  simp [incf, Function.update_of_ne h]

omit [Fintype ι] in
theorem decf_self (f : ι → ℕ) (i : ι) : decf f i i = f i - 1 := by
  simp [decf]

omit [Fintype ι] in
theorem decf_of_ne (f : ι → ℕ) {i k : ι} (h : k ≠ i) : decf f i k = f k := by
  simp [decf, Function.update_of_ne h]

theorem sum_update (f : ι → ℕ) (i : ι) (v : ℕ) :
    ∑ x, Function.update f i v x = v + ∑ x ∈ Finset.univ.erase i, f x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

theorem sum_eq_add_erase (f : ι → ℕ) (i : ι) :
    ∑ x, f x = f i + ∑ x ∈ Finset.univ.erase i, f x :=
  (Finset.add_sum_erase _ f (Finset.mem_univ i)).symm

omit [DecidableEq ι] in
theorem pair_le_sum (v : ι → ℕ) {i j : ι} (h : i ≠ j) : v i + v j ≤ ∑ k, v k := by
  classical
  have hsub := Finset.sum_le_sum_of_subset (f := v) (Finset.subset_univ ({i, j} : Finset ι))
  rwa [Finset.sum_pair h] at hsub

omit [DecidableEq ι] in
theorem triple_le_sum (v : ι → ℕ) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    v i + v j + v k ≤ ∑ l, v l := by
  classical
  have hsub := Finset.sum_le_sum_of_subset (f := v) (Finset.subset_univ ({i, j, k} : Finset ι))
  have hmem : i ∉ ({j, k} : Finset ι) := by simp [hij, hik]
  rw [Finset.sum_insert hmem, Finset.sum_pair hjk] at hsub
  omega

theorem sum_incf (f : ι → ℕ) (i : ι) : ∑ x, incf f i x = (∑ x, f x) + 1 := by
  rw [incf, sum_update, sum_eq_add_erase f i]; ring

theorem sum_decf {f : ι → ℕ} {i : ι} (h : f i ≠ 0) : (∑ x, decf f i x) + 1 = ∑ x, f x := by
  rw [decf, sum_update, sum_eq_add_erase f i]
  omega

structure Config (KA KB : ℕ) where
  a : Fin KA → ℕ
  b : Fin KB → ℕ
  c : Fin KA → Fin KB → ℕ

namespace Config

@[ext]
theorem ext {ξ η : Config KA KB} (ha : ξ.a = η.a) (hb : ξ.b = η.b) (hc : ξ.c = η.c) : ξ = η := by
  cases ξ; cases η; simp_all

def sumA (ξ : Config KA KB) : ℕ := ∑ i, ξ.a i

def sumB (ξ : Config KA KB) : ℕ := ∑ j, ξ.b j

def t (ξ : Config KA KB) : ℕ := ∑ i, ∑ j, ξ.c i j

def cRow (ξ : Config KA KB) (i : Fin KA) : ℕ := ∑ j, ξ.c i j

def cCol (ξ : Config KA KB) (j : Fin KB) : ℕ := ∑ i, ξ.c i j

def nA (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.t

def nB (ξ : Config KA KB) : ℕ := ξ.sumB + ξ.t

def n (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.sumB + ξ.t

def mA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.a i + ξ.cRow i

def mB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.b j + ξ.cCol j

theorem t_eq_sum_cRow (ξ : Config KA KB) : ξ.t = ∑ i, ξ.cRow i := rfl

theorem t_eq_sum_cCol (ξ : Config KA KB) : ξ.t = ∑ j, ξ.cCol j := by
  simp only [t, cCol]
  exact Finset.sum_comm

theorem sum_mA (ξ : Config KA KB) : ∑ i, ξ.mA i = ξ.nA := by
  simp [mA, nA, sumA, t_eq_sum_cRow, Finset.sum_add_distrib]

theorem sum_mB (ξ : Config KA KB) : ∑ j, ξ.mB j = ξ.nB := by
  simp [mB, nB, sumB, t_eq_sum_cCol, Finset.sum_add_distrib]

theorem n_add_t (ξ : Config KA KB) : ξ.n + ξ.t = ξ.nA + ξ.nB := by
  simp only [n, nA, nB]; ring

theorem sumA_le_nA (ξ : Config KA KB) : ξ.sumA ≤ ξ.nA := Nat.le_add_right _ _

theorem sumB_le_nB (ξ : Config KA KB) : ξ.sumB ≤ ξ.nB := Nat.le_add_right _ _

theorem t_le_nA (ξ : Config KA KB) : ξ.t ≤ ξ.nA := Nat.le_add_left _ _

theorem t_le_nB (ξ : Config KA KB) : ξ.t ≤ ξ.nB := Nat.le_add_left _ _

theorem sumA_add_sumB_le_n (ξ : Config KA KB) : ξ.sumA + ξ.sumB ≤ ξ.n := Nat.le_add_right _ _

theorem nA_le_n (ξ : Config KA KB) : ξ.nA ≤ ξ.n := by
  simp only [nA, n]; omega

theorem nB_le_n (ξ : Config KA KB) : ξ.nB ≤ ξ.n := by
  simp only [nB, n]; omega

theorem n_eq_zero_iff (ξ : Config KA KB) : ξ.n = 0 ↔ ξ.nA = 0 ∧ ξ.nB = 0 := by
  simp only [n, nA, nB]; omega

def incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (incf (m i) j)

def decC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (decf (m i) j)

theorem sum_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    ∑ i', ∑ j', incC m i j i' j' = (∑ i', ∑ j', m i' j') + 1 := by
  have h1 : ∀ i' : Fin KA, ∑ j', incC m i j i' j'
      = Function.update (fun i'' => ∑ j', m i'' j') i ((∑ j', m i j') + 1) i' := by
    intro i'
    by_cases h : i' = i
    · subst h; simp [incC, sum_incf]
    · simp [incC, Function.update_of_ne h]
  simp only [h1]
  rw [sum_update, sum_eq_add_erase (fun i' => ∑ j', m i' j') i]
  ring

theorem sum_decC {m : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0) :
    (∑ i', ∑ j', decC m i j i' j') + 1 = ∑ i', ∑ j', m i' j' := by
  have hpos : 1 ≤ ∑ j', m i j' := by
    have := Finset.single_le_sum (f := fun j' => m i j') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega
  have hd : ∑ j', decf (m i) j j' = (∑ j', m i j') - 1 := by
    have := sum_decf (f := m i) (i := j) h; omega
  have h1 : ∀ i' : Fin KA, ∑ j', decC m i j i' j'
      = Function.update (fun i'' => ∑ j', m i'' j') i ((∑ j', m i j') - 1) i' := by
    intro i'
    by_cases h' : i' = i
    · subst h'; simp [decC, hd]
    · simp [decC, Function.update_of_ne h']
  simp only [h1]
  rw [sum_update, sum_eq_add_erase (fun i' => ∑ j', m i' j') i]
  omega

def dropA (ξ : Config KA KB) (i : Fin KA) : Config KA KB := ⟨decf ξ.a i, ξ.b, ξ.c⟩

def dropB (ξ : Config KA KB) (j : Fin KB) : Config KA KB := ⟨ξ.a, decf ξ.b j, ξ.c⟩

def dropC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, ξ.b, decC ξ.c i j⟩

def mergeAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨decf ξ.a i, decf ξ.b j, incC ξ.c i j⟩

def killA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, incf ξ.b j, decC ξ.c i j⟩

def killB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, ξ.b, decC ξ.c i j⟩

def split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, incf ξ.b j, decC ξ.c i j⟩

section Moves

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)

@[simp] theorem sumB_dropA : (ξ.dropA i).sumB = ξ.sumB := rfl
@[simp] theorem t_dropA : (ξ.dropA i).t = ξ.t := rfl
@[simp] theorem sumA_dropB : (ξ.dropB j).sumA = ξ.sumA := rfl
@[simp] theorem t_dropB : (ξ.dropB j).t = ξ.t := rfl
@[simp] theorem sumA_dropC : (ξ.dropC i j).sumA = ξ.sumA := rfl
@[simp] theorem sumB_dropC : (ξ.dropC i j).sumB = ξ.sumB := rfl
@[simp] theorem sumA_killA : (ξ.killA i j).sumA = ξ.sumA := rfl
@[simp] theorem sumB_killB : (ξ.killB i j).sumB = ξ.sumB := rfl

theorem sumA_dropA (h : ξ.a i ≠ 0) : (ξ.dropA i).sumA + 1 = ξ.sumA := sum_decf h
theorem sumB_dropB (h : ξ.b j ≠ 0) : (ξ.dropB j).sumB + 1 = ξ.sumB := sum_decf h
theorem t_dropC (h : ξ.c i j ≠ 0) : (ξ.dropC i j).t + 1 = ξ.t := sum_decC h
theorem sumA_mergeAB (h : ξ.a i ≠ 0) : (ξ.mergeAB i j).sumA + 1 = ξ.sumA := sum_decf h
theorem sumB_mergeAB (h : ξ.b j ≠ 0) : (ξ.mergeAB i j).sumB + 1 = ξ.sumB := sum_decf h
theorem t_mergeAB : (ξ.mergeAB i j).t = ξ.t + 1 := sum_incC _ _ _
theorem sumB_killA : (ξ.killA i j).sumB = ξ.sumB + 1 := sum_incf _ _
theorem t_killA (h : ξ.c i j ≠ 0) : (ξ.killA i j).t + 1 = ξ.t := sum_decC h
theorem sumA_killB : (ξ.killB i j).sumA = ξ.sumA + 1 := sum_incf _ _
theorem t_killB (h : ξ.c i j ≠ 0) : (ξ.killB i j).t + 1 = ξ.t := sum_decC h
theorem sumA_split : (ξ.split i j).sumA = ξ.sumA + 1 := sum_incf _ _
theorem sumB_split : (ξ.split i j).sumB = ξ.sumB + 1 := sum_incf _ _
theorem t_split (h : ξ.c i j ≠ 0) : (ξ.split i j).t + 1 = ξ.t := sum_decC h

theorem nA_dropA (h : ξ.a i ≠ 0) : (ξ.dropA i).nA + 1 = ξ.nA := by
  have := sumA_dropA ξ i h; simp only [nA, t_dropA]; omega

@[simp] theorem nB_dropA : (ξ.dropA i).nB = ξ.nB := rfl

theorem n_dropA (h : ξ.a i ≠ 0) : (ξ.dropA i).n + 1 = ξ.n := by
  have := sumA_dropA ξ i h; simp only [n, t_dropA, sumB_dropA]; omega

@[simp] theorem nA_dropB : (ξ.dropB j).nA = ξ.nA := rfl

theorem nB_dropB (h : ξ.b j ≠ 0) : (ξ.dropB j).nB + 1 = ξ.nB := by
  have := sumB_dropB ξ j h; simp only [nB, t_dropB]; omega

theorem n_dropB (h : ξ.b j ≠ 0) : (ξ.dropB j).n + 1 = ξ.n := by
  have := sumB_dropB ξ j h; simp only [n, t_dropB, sumA_dropB]; omega

theorem nA_dropC (h : ξ.c i j ≠ 0) : (ξ.dropC i j).nA + 1 = ξ.nA := by
  have := t_dropC ξ i j h; simp only [nA, sumA_dropC]; omega

theorem nB_dropC (h : ξ.c i j ≠ 0) : (ξ.dropC i j).nB + 1 = ξ.nB := by
  have := t_dropC ξ i j h; simp only [nB, sumB_dropC]; omega

theorem n_dropC (h : ξ.c i j ≠ 0) : (ξ.dropC i j).n + 1 = ξ.n := by
  have := t_dropC ξ i j h; simp only [n, sumA_dropC, sumB_dropC]; omega

theorem nA_mergeAB (h : ξ.a i ≠ 0) : (ξ.mergeAB i j).nA = ξ.nA := by
  have := sumA_mergeAB ξ i j h
  simp only [nA, t_mergeAB]; omega

theorem nB_mergeAB (h : ξ.b j ≠ 0) : (ξ.mergeAB i j).nB = ξ.nB := by
  have := sumB_mergeAB ξ i j h
  simp only [nB, t_mergeAB]; omega

theorem n_mergeAB (ha : ξ.a i ≠ 0) (hb : ξ.b j ≠ 0) : (ξ.mergeAB i j).n + 1 = ξ.n := by
  have h1 := sumA_mergeAB ξ i j ha
  have h2 := sumB_mergeAB ξ i j hb
  simp only [n, t_mergeAB]; omega

theorem nA_killA (h : ξ.c i j ≠ 0) : (ξ.killA i j).nA + 1 = ξ.nA := by
  have := t_killA ξ i j h; simp only [nA, sumA_killA]; omega

theorem nB_killA (h : ξ.c i j ≠ 0) : (ξ.killA i j).nB = ξ.nB := by
  have := t_killA ξ i j h
  have := sumB_killA ξ i j
  simp only [nB]; omega

theorem n_killA (h : ξ.c i j ≠ 0) : (ξ.killA i j).n = ξ.n := by
  have := t_killA ξ i j h
  have := sumB_killA ξ i j
  simp only [n, sumA_killA]; omega

theorem nB_killB (h : ξ.c i j ≠ 0) : (ξ.killB i j).nB + 1 = ξ.nB := by
  have := t_killB ξ i j h; simp only [nB, sumB_killB]; omega

theorem nA_killB (h : ξ.c i j ≠ 0) : (ξ.killB i j).nA = ξ.nA := by
  have := t_killB ξ i j h
  have := sumA_killB ξ i j
  simp only [nA]; omega

theorem n_killB (h : ξ.c i j ≠ 0) : (ξ.killB i j).n = ξ.n := by
  have := t_killB ξ i j h
  have := sumA_killB ξ i j
  simp only [n, sumB_killB]; omega

theorem nA_split (h : ξ.c i j ≠ 0) : (ξ.split i j).nA = ξ.nA := by
  have := t_split ξ i j h
  have := sumA_split ξ i j
  simp only [nA]; omega

theorem nB_split (h : ξ.c i j ≠ 0) : (ξ.split i j).nB = ξ.nB := by
  have := t_split ξ i j h
  have := sumB_split ξ i j
  simp only [nB]; omega

theorem n_split (h : ξ.c i j ≠ 0) : (ξ.split i j).n = ξ.n + 1 := by
  have := t_split ξ i j h
  have := sumA_split ξ i j
  have := sumB_split ξ i j
  simp only [n]; omega

end Moves

section Marginals

theorem le_cRow (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ξ.c i j ≤ ξ.cRow i :=
  Finset.single_le_sum (f := fun j' => ξ.c i j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem le_cCol (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ξ.c i j ≤ ξ.cCol j :=
  Finset.single_le_sum (f := fun i' => ξ.c i' j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem cRow_ne_zero (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (h : ξ.c i j ≠ 0) :
    ξ.cRow i ≠ 0 := by
  have := ξ.le_cRow i j; omega

theorem cCol_ne_zero (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (h : ξ.c i j ≠ 0) :
    ξ.cCol j ≠ 0 := by
  have := ξ.le_cCol i j; omega

theorem decC_self (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (j' : Fin KB) :
    decC m i j i j' = decf (m i) j j' := by
  simp [decC]

theorem decC_of_ne (m : Fin KA → Fin KB → ℕ) {i i' : Fin KA} (j : Fin KB) (h : i' ≠ i)
    (j' : Fin KB) : decC m i j i' j' = m i' j' := by
  simp [decC, Function.update_of_ne h]

theorem incC_self (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (j' : Fin KB) :
    incC m i j i j' = incf (m i) j j' := by
  simp [incC]

theorem incC_of_ne (m : Fin KA → Fin KB → ℕ) {i i' : Fin KA} (j : Fin KB) (h : i' ≠ i)
    (j' : Fin KB) : incC m i j i' j' = m i' j' := by
  simp [incC, Function.update_of_ne h]

theorem sum_row_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (k : Fin KA) :
    (∑ l, incC m i j k l) = incf (fun k' => ∑ l, m k' l) i k := by
  by_cases hk : k = i
  · subst hk
    rw [incf_self]
    simp only [incC, Function.update_self]
    exact sum_incf (m k) j
  · rw [incf_of_ne _ hk]
    simp [incC, Function.update_of_ne hk]

theorem sum_col_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (l : Fin KB) :
    (∑ k, incC m i j k l) = incf (fun l' => ∑ k, m k l') j l := by
  have hfun : ∀ k : Fin KA,
      incC m i j k l = m k l + (if k = i then (if l = j then 1 else 0) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = j
      · subst hl; simp [incC, incf_self]
      · simp [incC, incf_of_ne _ hl, hl]
    · simp [incC, hk]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hfun k, Finset.sum_add_distrib]
  by_cases hl : l = j
  · subst hl
    rw [incf_self]
    simp
  · rw [incf_of_ne _ hl]
    simp [hl]

theorem sum_row_decC {m : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0)
    (k : Fin KA) : (∑ l, decC m i j k l) = decf (fun k' => ∑ l, m k' l) i k := by
  by_cases hk : k = i
  · subst hk
    rw [decf_self]
    simp only [decC, Function.update_self]
    have := sum_decf (f := m k) (i := j) h
    omega
  · rw [decf_of_ne _ hk]
    simp [decC, Function.update_of_ne hk]

theorem sum_col_decC {m : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0)
    (l : Fin KB) : (∑ k, decC m i j k l) = decf (fun l' => ∑ k, m k l') j l := by
  have hi : ∀ k ∈ Finset.univ.erase i, decC m i j k l = m k l := by
    intro k hk
    simp [decC, Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [sum_eq_add_erase (fun k => decC m i j k l) i, Finset.sum_congr rfl hi]
  have hcol : (∑ k, m k l) = m i l + ∑ k ∈ Finset.univ.erase i, m k l :=
    sum_eq_add_erase (fun k => m k l) i
  have hii : decC m i j i l = decf (m i) j l := by simp [decC]
  rw [hii]
  by_cases hl : l = j
  · subst hl
    rw [decf_self, decf_self]
    omega
  · rw [decf_of_ne _ hl, decf_of_ne _ hl]
    omega

theorem cRow_dropC (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.dropC i₀ j₀).cRow = decf ξ.cRow i₀ :=
  funext fun i => sum_row_decC h i

theorem cCol_dropC (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.dropC i₀ j₀).cCol = decf ξ.cCol j₀ :=
  funext fun j => sum_col_decC h j

theorem cRow_incC (ξ : Config KA KB) (i₀ : Fin KA) (j₀ : Fin KB) :
    (ξ.mergeAB i₀ j₀).cRow = incf ξ.cRow i₀ :=
  funext fun i => sum_row_incC ξ.c i₀ j₀ i

theorem cCol_incC (ξ : Config KA KB) (i₀ : Fin KA) (j₀ : Fin KB) :
    (ξ.mergeAB i₀ j₀).cCol = incf ξ.cCol j₀ :=
  funext fun j => sum_col_incC ξ.c i₀ j₀ j

theorem cRow_split (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.split i₀ j₀).cRow = decf ξ.cRow i₀ := ξ.cRow_dropC h

theorem cCol_split (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.split i₀ j₀).cCol = decf ξ.cCol j₀ := ξ.cCol_dropC h

theorem c_split (ξ : Config KA KB) (i₀ : Fin KA) (j₀ : Fin KB) :
    (ξ.split i₀ j₀).c = decC ξ.c i₀ j₀ := rfl

theorem mA_dropA (ξ : Config KA KB) {i₀ : Fin KA} (h : ξ.a i₀ ≠ 0) :
    (ξ.dropA i₀).mA = decf ξ.mA i₀ := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    change decf ξ.a i i + ξ.cRow i = decf ξ.mA i i
    rw [decf_self, decf_self]
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change decf ξ.a i₀ i + ξ.cRow i = decf ξ.mA i₀ i
    rw [decf_of_ne _ hi, decf_of_ne _ hi]
    rfl

@[simp] theorem mB_dropA (ξ : Config KA KB) (i₀ : Fin KA) : (ξ.dropA i₀).mB = ξ.mB := rfl

@[simp] theorem mA_dropB (ξ : Config KA KB) (j₀ : Fin KB) : (ξ.dropB j₀).mA = ξ.mA := rfl

theorem mB_dropB (ξ : Config KA KB) {j₀ : Fin KB} (h : ξ.b j₀ ≠ 0) :
    (ξ.dropB j₀).mB = decf ξ.mB j₀ := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    change decf ξ.b j j + ξ.cCol j = decf ξ.mB j j
    rw [decf_self, decf_self]
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change decf ξ.b j₀ j + ξ.cCol j = decf ξ.mB j₀ j
    rw [decf_of_ne _ hj, decf_of_ne _ hj]
    rfl

theorem mA_dropC (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.dropC i₀ j₀).mA = decf ξ.mA i₀ := by
  funext i
  have hrow := congrFun (ξ.cRow_dropC h) i
  by_cases hi : i = i₀
  · subst hi
    change ξ.a i + (ξ.dropC i j₀).cRow i = decf ξ.mA i i
    rw [hrow, decf_self, decf_self]
    have hle : 1 ≤ ξ.cRow i := by have := ξ.le_cRow i j₀; omega
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change ξ.a i + (ξ.dropC i₀ j₀).cRow i = decf ξ.mA i₀ i
    rw [hrow, decf_of_ne _ hi, decf_of_ne _ hi]
    rfl

theorem mB_dropC (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.dropC i₀ j₀).mB = decf ξ.mB j₀ := by
  funext j
  have hcol := congrFun (ξ.cCol_dropC h) j
  by_cases hj : j = j₀
  · subst hj
    change ξ.b j + (ξ.dropC i₀ j).cCol j = decf ξ.mB j j
    rw [hcol, decf_self, decf_self]
    have hle : 1 ≤ ξ.cCol j := by have := ξ.le_cCol i₀ j; omega
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change ξ.b j + (ξ.dropC i₀ j₀).cCol j = decf ξ.mB j₀ j
    rw [hcol, decf_of_ne _ hj, decf_of_ne _ hj]
    rfl

theorem mA_mergeAB (ξ : Config KA KB) {i₀ : Fin KA} (j₀ : Fin KB) (h : ξ.a i₀ ≠ 0) :
    (ξ.mergeAB i₀ j₀).mA = ξ.mA := by
  funext i
  have hrow := congrFun (ξ.cRow_incC i₀ j₀) i
  by_cases hi : i = i₀
  · subst hi
    change decf ξ.a i i + (ξ.mergeAB i j₀).cRow i = ξ.mA i
    rw [hrow, decf_self, incf_self]
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change decf ξ.a i₀ i + (ξ.mergeAB i₀ j₀).cRow i = ξ.mA i
    rw [hrow, decf_of_ne _ hi, incf_of_ne _ hi]
    rfl

theorem mB_mergeAB (ξ : Config KA KB) (i₀ : Fin KA) {j₀ : Fin KB} (h : ξ.b j₀ ≠ 0) :
    (ξ.mergeAB i₀ j₀).mB = ξ.mB := by
  funext j
  have hcol := congrFun (ξ.cCol_incC i₀ j₀) j
  by_cases hj : j = j₀
  · subst hj
    change decf ξ.b j j + (ξ.mergeAB i₀ j).cCol j = ξ.mB j
    rw [hcol, decf_self, incf_self]
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change decf ξ.b j₀ j + (ξ.mergeAB i₀ j₀).cCol j = ξ.mB j
    rw [hcol, decf_of_ne _ hj, incf_of_ne _ hj]
    rfl

theorem mA_killA (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.killA i₀ j₀).mA = decf ξ.mA i₀ := by
  have hd : (ξ.killA i₀ j₀).cRow = (ξ.dropC i₀ j₀).cRow := rfl
  funext i
  have hrow := congrFun (ξ.cRow_dropC h) i
  rw [← hd] at hrow
  by_cases hi : i = i₀
  · subst hi
    change ξ.a i + (ξ.killA i j₀).cRow i = decf ξ.mA i i
    rw [hrow, decf_self, decf_self]
    have hle : 1 ≤ ξ.cRow i := by have := ξ.le_cRow i j₀; omega
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change ξ.a i + (ξ.killA i₀ j₀).cRow i = decf ξ.mA i₀ i
    rw [hrow, decf_of_ne _ hi, decf_of_ne _ hi]
    rfl

theorem mB_killA (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.killA i₀ j₀).mB = ξ.mB := by
  have hd : (ξ.killA i₀ j₀).cCol = (ξ.dropC i₀ j₀).cCol := rfl
  funext j
  have hcol := congrFun (ξ.cCol_dropC h) j
  rw [← hd] at hcol
  by_cases hj : j = j₀
  · subst hj
    change incf ξ.b j j + (ξ.killA i₀ j).cCol j = ξ.mB j
    rw [hcol, incf_self, decf_self]
    have hle : 1 ≤ ξ.cCol j := by have := ξ.le_cCol i₀ j; omega
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change incf ξ.b j₀ j + (ξ.killA i₀ j₀).cCol j = ξ.mB j
    rw [hcol, incf_of_ne _ hj, decf_of_ne _ hj]
    rfl

theorem mA_killB (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.killB i₀ j₀).mA = ξ.mA := by
  have hd : (ξ.killB i₀ j₀).cRow = (ξ.dropC i₀ j₀).cRow := rfl
  funext i
  have hrow := congrFun (ξ.cRow_dropC h) i
  rw [← hd] at hrow
  by_cases hi : i = i₀
  · subst hi
    change incf ξ.a i i + (ξ.killB i j₀).cRow i = ξ.mA i
    rw [hrow, incf_self, decf_self]
    have hle : 1 ≤ ξ.cRow i := by have := ξ.le_cRow i j₀; omega
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change incf ξ.a i₀ i + (ξ.killB i₀ j₀).cRow i = ξ.mA i
    rw [hrow, incf_of_ne _ hi, decf_of_ne _ hi]
    rfl

theorem mB_killB (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.killB i₀ j₀).mB = decf ξ.mB j₀ := by
  have hd : (ξ.killB i₀ j₀).cCol = (ξ.dropC i₀ j₀).cCol := rfl
  funext j
  have hcol := congrFun (ξ.cCol_dropC h) j
  rw [← hd] at hcol
  by_cases hj : j = j₀
  · subst hj
    change ξ.b j + (ξ.killB i₀ j).cCol j = decf ξ.mB j j
    rw [hcol, decf_self, decf_self]
    have hle : 1 ≤ ξ.cCol j := by have := ξ.le_cCol i₀ j; omega
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change ξ.b j + (ξ.killB i₀ j₀).cCol j = decf ξ.mB j₀ j
    rw [hcol, decf_of_ne _ hj, decf_of_ne _ hj]
    rfl

theorem mA_split (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.split i₀ j₀).mA = ξ.mA := by
  have hd : (ξ.split i₀ j₀).cRow = (ξ.dropC i₀ j₀).cRow := rfl
  funext i
  have hrow := congrFun (ξ.cRow_dropC h) i
  rw [← hd] at hrow
  by_cases hi : i = i₀
  · subst hi
    change incf ξ.a i i + (ξ.split i j₀).cRow i = ξ.mA i
    rw [hrow, incf_self, decf_self]
    have hle : 1 ≤ ξ.cRow i := by have := ξ.le_cRow i j₀; omega
    have hm : ξ.mA i = ξ.a i + ξ.cRow i := rfl
    omega
  · change incf ξ.a i₀ i + (ξ.split i₀ j₀).cRow i = ξ.mA i
    rw [hrow, incf_of_ne _ hi, decf_of_ne _ hi]
    rfl

theorem mB_split (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB} (h : ξ.c i₀ j₀ ≠ 0) :
    (ξ.split i₀ j₀).mB = ξ.mB := by
  have hd : (ξ.split i₀ j₀).cCol = (ξ.dropC i₀ j₀).cCol := rfl
  funext j
  have hcol := congrFun (ξ.cCol_dropC h) j
  rw [← hd] at hcol
  by_cases hj : j = j₀
  · subst hj
    change incf ξ.b j j + (ξ.split i₀ j).cCol j = ξ.mB j
    rw [hcol, incf_self, decf_self]
    have hle : 1 ≤ ξ.cCol j := by have := ξ.le_cCol i₀ j; omega
    have hm : ξ.mB j = ξ.b j + ξ.cCol j := rfl
    omega
  · change incf ξ.b j₀ j + (ξ.split i₀ j₀).cCol j = ξ.mB j
    rw [hcol, incf_of_ne _ hj, decf_of_ne _ hj]
    rfl

end Marginals

instance : Zero (Config KA KB) := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩

@[simp] theorem zero_a (i : Fin KA) : (0 : Config KA KB).a i = 0 := rfl
@[simp] theorem zero_b (j : Fin KB) : (0 : Config KA KB).b j = 0 := rfl
@[simp] theorem zero_c (i : Fin KA) (j : Fin KB) : (0 : Config KA KB).c i j = 0 := rfl

def eA (i : Fin KA) : Config KA KB := ⟨incf (fun _ => 0) i, fun _ => 0, fun _ _ => 0⟩

def eB (j : Fin KB) : Config KA KB := ⟨fun _ => 0, incf (fun _ => 0) j, fun _ _ => 0⟩

def eC (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, incC (fun _ _ => 0) i j⟩

@[simp] theorem sumA_zero : (0 : Config KA KB).sumA = 0 := by simp [sumA]
@[simp] theorem sumB_zero : (0 : Config KA KB).sumB = 0 := by simp [sumB]
@[simp] theorem t_zero : (0 : Config KA KB).t = 0 := by simp [t]
@[simp] theorem n_zero : (0 : Config KA KB).n = 0 := by simp [n]
@[simp] theorem nA_zero : (0 : Config KA KB).nA = 0 := by simp [nA]
@[simp] theorem nB_zero : (0 : Config KA KB).nB = 0 := by simp [nB]

@[simp] theorem n_eA (i : Fin KA) : (eA i : Config KA KB).n = 1 := by
  simp [eA, n, sumA, sumB, t, sum_incf]

@[simp] theorem n_eB (j : Fin KB) : (eB j : Config KA KB).n = 1 := by
  simp [eB, n, sumA, sumB, t, sum_incf]

@[simp] theorem n_eC (i : Fin KA) (j : Fin KB) : (eC i j : Config KA KB).n = 1 := by
  simp [eC, n, sumA, sumB, t, sum_incC]

@[simp] theorem mA_zero : (0 : Config KA KB).mA = fun _ => 0 := by
  funext i; simp [mA, cRow]

@[simp] theorem mB_zero : (0 : Config KA KB).mB = fun _ => 0 := by
  funext j; simp [mB, cCol]

@[simp] theorem mA_eA (i : Fin KA) : (eA i : Config KA KB).mA = incf (fun _ => 0) i := by
  funext k; simp [mA, cRow, eA]

@[simp] theorem mB_eA (i : Fin KA) : (eA i : Config KA KB).mB = fun _ => 0 := by
  funext l; simp [mB, cCol, eA]

@[simp] theorem mA_eB (j : Fin KB) : (eB j : Config KA KB).mA = fun _ => 0 := by
  funext k; simp [mA, cRow, eB]

@[simp] theorem mB_eB (j : Fin KB) : (eB j : Config KA KB).mB = incf (fun _ => 0) j := by
  funext l; simp [mB, cCol, eB]

@[simp] theorem mA_eC (i : Fin KA) (j : Fin KB) :
    (eC i j : Config KA KB).mA = incf (fun _ => 0) i := by
  funext k
  have := sum_row_incC (fun (_ : Fin KA) (_ : Fin KB) => (0 : ℕ)) i j k
  simp only [mA, cRow, eC] at this ⊢
  simpa using this

@[simp] theorem mB_eC (i : Fin KA) (j : Fin KB) :
    (eC i j : Config KA KB).mB = incf (fun _ => 0) j := by
  funext l
  have := sum_col_incC (fun (_ : Fin KA) (_ : Fin KB) => (0 : ℕ)) i j l
  simp only [mB, cCol, eC] at this ⊢
  simpa using this

end Config

def eV (i : Fin KA) : Fin KA → ℕ := fun i' => if i' = i then 1 else 0

def eM (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ := fun i' => if i' = i then eV j else 0

@[simp] theorem eV_self (i : Fin KA) : eV i i = 1 := by simp [eV]

theorem eV_of_ne {i i' : Fin KA} (h : i' ≠ i) : eV i i' = 0 := by simp [eV, h]

theorem eM_apply (i : Fin KA) (j : Fin KB) (i' : Fin KA) (j' : Fin KB) :
    eM i j i' j' = if i' = i then (if j' = j then 1 else 0) else 0 := by
  by_cases h : i' = i <;> simp [eM, eV, h]

theorem incf_eq_add (f : Fin KA → ℕ) (i : Fin KA) : incf f i = eV i + f := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [incf_self, eV, Nat.add_comm]
  · simp [incf_of_ne f h, eV_of_ne h]

theorem decf_eV_add (f : Fin KA → ℕ) (i : Fin KA) : decf (eV i + f) i = f := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [decf_self, eV]
  · simp [decf_of_ne _ h, eV_of_ne h]

theorem incC_eq_add (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    Config.incC m i j = eM i j + m := by
  funext i' j'
  by_cases h : i' = i
  · subst h; simp [Config.incC, incf_eq_add, eM]
  · simp [Config.incC, eM, h]

theorem decC_eM_add (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    Config.decC (eM i j + m) i j = m := by
  funext i' j'
  by_cases h : i' = i
  · subst h
    have hrow : (eM i' j + m) i' = eV j + m i' := by
      funext j''; simp [eM]
    simp only [Config.decC, Function.update_self, hrow]
    exact congrFun (decf_eV_add (m i') j) j'
  · simp [Config.decC, eM, h]

end Rhone.LinearAlgebra.Recursion
