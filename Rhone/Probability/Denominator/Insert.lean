/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.OneLocus
public import Rhone.LinearAlgebra.Recursion.Bookkeeping

/-! # Inserting one A-typed slot into a configuration -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ}

section Pointwise

variable {ι : Type*} [DecidableEq ι]

theorem incf_apply (f : ι → ℕ) (i x : ι) : incf f i x = f x + (if x = i then 1 else 0) := by
  by_cases h : x = i
  · subst h; simp [incf_self]
  · simp [incf_of_ne _ h, h]

theorem decf_apply (f : ι → ℕ) (i x : ι) : decf f i x = f x - (if x = i then 1 else 0) := by
  by_cases h : x = i
  · subst h; simp [decf_self]
  · simp [decf_of_ne _ h, h]

theorem incf_comm (f : ι → ℕ) (i k : ι) : incf (incf f i) k = incf (incf f k) i := by
  funext x; simp only [incf_apply]; split_ifs <;> omega

theorem decf_comm (f : ι → ℕ) (i k : ι) : decf (decf f i) k = decf (decf f k) i := by
  funext x; simp only [decf_apply]; split_ifs <;> omega

theorem decf_incf_of_ne (f : ι → ℕ) {i k : ι} (h : k ≠ i) :
    decf (incf f i) k = incf (decf f k) i := by
  funext x
  simp only [incf_apply, decf_apply]
  by_cases h1 : x = i <;> by_cases h2 : x = k <;> simp_all

@[simp] theorem decf_incf_self (f : ι → ℕ) (i : ι) : decf (incf f i) i = f := by
  funext x; simp only [incf_apply, decf_apply]; split_ifs <;> omega

theorem incf_decf_self {f : ι → ℕ} {i : ι} (h : f i ≠ 0) : incf (decf f i) i = f := by
  funext x
  simp only [incf_apply, decf_apply]
  by_cases hx : x = i
  · subst hx
    have hone : (if x = x then 1 else 0) = 1 := ite_eq_left rfl
    rw [hone]
    omega
  · simp [hx]

theorem incf_decf_comm {f : ι → ℕ} {j : ι} (h : f j ≠ 0) (l : ι) :
    incf (decf f j) l = decf (incf f l) j := by
  funext x
  simp only [incf_apply, decf_apply]
  by_cases h1 : x = j <;> by_cases h2 : x = l <;> simp_all
  all_goals omega

end Pointwise

theorem incC_apply (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (k : Fin KA)
    (l : Fin KB) :
    Config.incC m i j k l = m k l + (if k = i then (if l = j then 1 else 0) else 0) := by
  by_cases h : k = i
  · subst h; simp [Config.incC, incf_apply]
  · simp [Config.incC, h]

theorem decC_apply (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (k : Fin KA)
    (l : Fin KB) :
    Config.decC m i j k l = m k l - (if k = i then (if l = j then 1 else 0) else 0) := by
  by_cases h : k = i
  · subst h; simp [Config.decC, decf_apply]
  · simp [Config.decC, h]

theorem incC_comm (m : Fin KA → Fin KB → ℕ) (i k : Fin KA) (j l : Fin KB) :
    Config.incC (Config.incC m i j) k l = Config.incC (Config.incC m k l) i j := by
  funext x y; simp only [incC_apply]; split_ifs <;> omega

@[simp] theorem decC_incC_self (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    Config.decC (Config.incC m i j) i j = m := by
  funext x y; simp only [incC_apply, decC_apply]; split_ifs <;> omega

theorem decC_incC_of_ne (m : Fin KA → Fin KB → ℕ) {i k : Fin KA} {j l : Fin KB}
    (h : ¬(k = i ∧ l = j)) :
    Config.decC (Config.incC m i j) k l = Config.incC (Config.decC m k l) i j := by
  funext x y
  simp only [incC_apply, decC_apply]
  by_cases h1 : x = i <;> by_cases h2 : x = k <;> by_cases h3 : y = j <;> by_cases h4 : y = l <;>
    simp_all

def addA (ξ : Config KA KB) (i : Fin KA) : Config KA KB := ⟨incf ξ.a i, ξ.b, ξ.c⟩

def addB (ξ : Config KA KB) (j : Fin KB) : Config KA KB := ⟨ξ.a, incf ξ.b j, ξ.c⟩

def addC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, ξ.b, Config.incC ξ.c i j⟩

def up (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, decf ξ.b j, Config.incC ξ.c i j⟩

theorem up_addB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : up (addB ξ j) i j = addC ξ i j :=
  Config.ext rfl (by simp [addB, up, addC]) rfl

theorem addB_dropB {ξ : Config KA KB} {j : Fin KB} (h : ξ.b j ≠ 0) : addB (ξ.dropB j) j = ξ :=
  Config.ext rfl (by simp [addB, Config.dropB, incf_decf_self h]) rfl

section Counts

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)

@[simp] theorem t_addA : (addA ξ i).t = ξ.t := rfl
@[simp] theorem cRow_addA (k : Fin KA) : (addA ξ i).cRow k = ξ.cRow k := rfl
@[simp] theorem cCol_addA (l : Fin KB) : (addA ξ i).cCol l = ξ.cCol l := rfl
@[simp] theorem b_addA (l : Fin KB) : (addA ξ i).b l = ξ.b l := rfl
@[simp] theorem c_addA (k : Fin KA) (l : Fin KB) : (addA ξ i).c k l = ξ.c k l := rfl
@[simp] theorem a_addA (k : Fin KA) : (addA ξ i).a k = incf ξ.a i k := rfl

@[simp] theorem sumA_addA : (addA ξ i).sumA = ξ.sumA + 1 := sum_incf ξ.a i
@[simp] theorem sumB_addA : (addA ξ i).sumB = ξ.sumB := rfl

theorem nA_addA : (addA ξ i).nA = ξ.nA + 1 := by
  simp only [Config.nA, sumA_addA, t_addA]; omega

@[simp] theorem nB_addA : (addA ξ i).nB = ξ.nB := rfl

theorem n_addA : (addA ξ i).n = ξ.n + 1 := by
  simp only [Config.n, sumA_addA, sumB_addA, t_addA]; omega

@[simp] theorem a_up (k : Fin KA) : (up ξ i j).a k = ξ.a k := rfl
@[simp] theorem b_up (l : Fin KB) : (up ξ i j).b l = decf ξ.b j l := rfl
@[simp] theorem c_up (k : Fin KA) (l : Fin KB) : (up ξ i j).c k l = Config.incC ξ.c i j k l := rfl
@[simp] theorem sumA_up : (up ξ i j).sumA = ξ.sumA := rfl

theorem sumB_up (h : ξ.b j ≠ 0) : (up ξ i j).sumB + 1 = ξ.sumB := sum_decf h

theorem t_up : (up ξ i j).t = ξ.t + 1 := Config.sum_incC ξ.c i j

theorem cRow_up (k : Fin KA) : (up ξ i j).cRow k = ξ.cRow k + (if k = i then 1 else 0) := by
  have := Config.sum_row_incC ξ.c i j k
  simp only [Config.cRow, up] at this ⊢
  rw [this, incf_apply]

theorem cCol_up (l : Fin KB) : (up ξ i j).cCol l = ξ.cCol l + (if l = j then 1 else 0) := by
  have := Config.sum_col_incC ξ.c i j l
  simp only [Config.cCol, up] at this ⊢
  rw [this, incf_apply]

theorem nA_up : (up ξ i j).nA = ξ.nA + 1 := by
  have h1 : (up ξ i j).sumA = ξ.sumA := rfl
  have h2 := t_up ξ i j
  simp only [Config.nA]; omega

theorem nB_up (h : ξ.b j ≠ 0) : (up ξ i j).nB = ξ.nB := by
  have h1 := sumB_up ξ i j h
  have h2 := t_up ξ i j
  simp only [Config.nB]; omega

theorem n_up (h : ξ.b j ≠ 0) : (up ξ i j).n = ξ.n := by
  have h1 := sumB_up ξ i j h
  have h2 := t_up ξ i j
  have h3 : (up ξ i j).sumA = ξ.sumA := rfl
  simp only [Config.n]; omega

@[simp] theorem sumA_addB (l : Fin KB) : (addB ξ l).sumA = ξ.sumA := rfl
@[simp] theorem t_addB (l : Fin KB) : (addB ξ l).t = ξ.t := rfl

theorem nA_addB (l : Fin KB) : (addB ξ l).nA = ξ.nA := rfl

theorem nB_addB (l : Fin KB) : (addB ξ l).nB = ξ.nB + 1 := by
  have : (addB ξ l).sumB = ξ.sumB + 1 := sum_incf ξ.b l
  simp only [Config.nB, t_addB]; omega

theorem mA_addA (k : Fin KA) : (addA ξ k).mA = incf ξ.mA k := by
  funext x
  by_cases hx : x = k
  · subst hx
    change incf ξ.a x x + ξ.cRow x = incf ξ.mA x x
    rw [incf_self, incf_self]
    change ξ.a x + 1 + ξ.cRow x = ξ.a x + ξ.cRow x + 1
    omega
  · change incf ξ.a k x + ξ.cRow x = incf ξ.mA k x
    rw [incf_of_ne _ hx, incf_of_ne _ hx]
    rfl

@[simp] theorem mB_addA (k : Fin KA) : (addA ξ k).mB = ξ.mB := rfl

theorem mB_addB (l : Fin KB) : (addB ξ l).mB = incf ξ.mB l := by
  funext y
  by_cases hy : y = l
  · subst hy
    change incf ξ.b y y + ξ.cCol y = incf ξ.mB y y
    rw [incf_self, incf_self]
    change ξ.b y + 1 + ξ.cCol y = ξ.b y + ξ.cCol y + 1
    omega
  · change incf ξ.b l y + ξ.cCol y = incf ξ.mB l y
    rw [incf_of_ne _ hy, incf_of_ne _ hy]
    rfl

@[simp] theorem mA_addB (l : Fin KB) : (addB ξ l).mA = ξ.mA := rfl

theorem mA_addC (k : Fin KA) (l : Fin KB) : (addC ξ k l).mA = incf ξ.mA k := by
  funext x
  have hrow : (addC ξ k l).cRow x = incf ξ.cRow k x := Config.sum_row_incC ξ.c k l x
  by_cases hx : x = k
  · subst hx
    change ξ.a x + (addC ξ x l).cRow x = incf ξ.mA x x
    rw [hrow, incf_self, incf_self]
    change ξ.a x + (ξ.cRow x + 1) = ξ.a x + ξ.cRow x + 1
    omega
  · change ξ.a x + (addC ξ k l).cRow x = incf ξ.mA k x
    rw [hrow, incf_of_ne _ hx, incf_of_ne _ hx]
    rfl

theorem mB_addC (k : Fin KA) (l : Fin KB) : (addC ξ k l).mB = incf ξ.mB l := by
  funext y
  have hcol : (addC ξ k l).cCol y = incf ξ.cCol l y := Config.sum_col_incC ξ.c k l y
  by_cases hy : y = l
  · subst hy
    change ξ.b y + (addC ξ k y).cCol y = incf ξ.mB y y
    rw [hcol, incf_self, incf_self]
    change ξ.b y + (ξ.cCol y + 1) = ξ.b y + ξ.cCol y + 1
    omega
  · change ξ.b y + (addC ξ k l).cCol y = incf ξ.mB l y
    rw [hcol, incf_of_ne _ hy, incf_of_ne _ hy]
    rfl

end Counts

section AddA

variable (ξ : Config KA KB) (i k : Fin KA) (l : Fin KB)

@[simp] theorem dropA_addA_self : (addA ξ i).dropA i = ξ :=
  Config.ext (by simp [addA, Config.dropA]) rfl rfl

theorem dropA_addA_of_ne (h : k ≠ i) : (addA ξ i).dropA k = addA (ξ.dropA k) i :=
  Config.ext (by simp [addA, Config.dropA, decf_incf_of_ne _ h]) rfl rfl

@[simp] theorem dropB_addA : (addA ξ i).dropB l = addA (ξ.dropB l) i := rfl

@[simp] theorem dropC_addA : (addA ξ i).dropC k l = addA (ξ.dropC k l) i := rfl

theorem mergeAB_addA_self : (addA ξ i).mergeAB i l = up ξ i l :=
  Config.ext (by simp [addA, Config.mergeAB, up]) rfl rfl

theorem mergeAB_addA_of_ne (h : k ≠ i) : (addA ξ i).mergeAB k l = addA (ξ.mergeAB k l) i :=
  Config.ext (by simp [addA, Config.mergeAB, decf_incf_of_ne _ h]) rfl rfl

@[simp] theorem killA_addA : (addA ξ i).killA k l = addA (ξ.killA k l) i := rfl

@[simp] theorem killB_addA : (addA ξ i).killB k l = addA (ξ.killB k l) i :=
  Config.ext (by simp [addA, Config.killB, incf_comm]) rfl rfl

@[simp] theorem split_addA : (addA ξ i).split k l = addA (ξ.split k l) i :=
  Config.ext (by simp [addA, Config.split, incf_comm]) rfl rfl

end AddA

section Up

variable (ξ : Config KA KB) (i k : Fin KA) (j l : Fin KB)

@[simp] theorem dropA_up : (up ξ i j).dropA k = up (ξ.dropA k) i j := rfl

@[simp] theorem dropB_up : (up ξ i j).dropB l = up (ξ.dropB l) i j :=
  Config.ext rfl (by simp [up, Config.dropB, decf_comm]) rfl

theorem dropC_up_self : (up ξ i j).dropC i j = ξ.dropB j :=
  Config.ext rfl rfl (by simp [up, Config.dropC, Config.dropB])

theorem dropC_up_of_ne (h : ¬(k = i ∧ l = j)) :
    (up ξ i j).dropC k l = up (ξ.dropC k l) i j :=
  Config.ext rfl rfl (by simp [up, Config.dropC, decC_incC_of_ne _ h])

@[simp] theorem mergeAB_up : (up ξ i j).mergeAB k l = up (ξ.mergeAB k l) i j :=
  Config.ext rfl (by simp [up, Config.mergeAB, decf_comm]) (by simp [up, Config.mergeAB, incC_comm])

theorem killA_up_self (h : ξ.b j ≠ 0) : (up ξ i j).killA i j = ξ :=
  Config.ext rfl (by simp [up, Config.killA, incf_decf_self h]) (by simp [up, Config.killA])

theorem killA_up_of_ne (h : ξ.b j ≠ 0) (hne : ¬(k = i ∧ l = j)) :
    (up ξ i j).killA k l = up (ξ.killA k l) i j :=
  Config.ext rfl (by simp [up, Config.killA, incf_decf_comm h])
    (by simp [up, Config.killA, decC_incC_of_ne _ hne])

theorem killB_up_self : (up ξ i j).killB i j = addA (ξ.dropB j) i :=
  Config.ext rfl rfl (by simp [up, Config.killB, addA, Config.dropB])

theorem killB_up_of_ne (hne : ¬(k = i ∧ l = j)) :
    (up ξ i j).killB k l = up (ξ.killB k l) i j :=
  Config.ext rfl rfl (by simp [up, Config.killB, decC_incC_of_ne _ hne])

theorem split_up_self (h : ξ.b j ≠ 0) : (up ξ i j).split i j = addA ξ i :=
  Config.ext rfl (by simp [up, Config.split, addA, incf_decf_self h])
    (by simp [up, Config.split, addA])

theorem split_up_of_ne (h : ξ.b j ≠ 0) (hne : ¬(k = i ∧ l = j)) :
    (up ξ i j).split k l = up (ξ.split k l) i j :=
  Config.ext rfl (by simp [up, Config.split, incf_decf_comm h])
    (by simp [up, Config.split, decC_incC_of_ne _ hne])

end Up

end Rhone.Probability.Denominator
