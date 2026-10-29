/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Exist

/-! # Boundary value `q(0,0,e_ij) = 1` is implied by the infinite-alleles recursion -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*}

def eAB (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf (fun _ => 0) i, incf (fun _ => 0) j, fun _ _ => 0⟩

section Nat

variable {i : Fin KA} {j : Fin KB}

theorem incf_zero_apply (i k : Fin KA) :
    incf (fun _ => 0) i k = if k = i then 1 else 0 := by
  by_cases h : k = i
  · subst h; simp [incf_self]
  · simp [incf_of_ne _ h, h]

@[simp] theorem eC_a (i' : Fin KA) : (Config.eC i j : Config KA KB).a i' = 0 := rfl

@[simp] theorem eC_b (j' : Fin KB) : (Config.eC i j : Config KA KB).b j' = 0 := rfl

theorem eC_c (i' : Fin KA) (j' : Fin KB) :
    (Config.eC i j : Config KA KB).c i' j' = if i' = i then (if j' = j then 1 else 0) else 0 := by
  by_cases h : i' = i
  · subst h
    simp only [Config.eC, incC, Function.update_self]
    exact incf_zero_apply j j'
  · simp [Config.eC, incC, h]

theorem eC_cRow (i' : Fin KA) :
    (Config.eC i j : Config KA KB).cRow i' = if i' = i then 1 else 0 := by
  simp only [Config.cRow, eC_c]
  by_cases h : i' = i
  · simp only [h, ite_true]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (fun hb => absurd (mem_univ j) hb)]
    simp
  · simp [h]

theorem eC_cCol (j' : Fin KB) :
    (Config.eC i j : Config KA KB).cCol j' = if j' = j then 1 else 0 := by
  simp only [Config.cCol, eC_c]
  by_cases h : j' = j
  · simp only [h, ite_true]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (fun hb => absurd (mem_univ i) hb)]
    simp
  · simp [h]

theorem eC_mA (i' : Fin KA) :
    (Config.eC i j : Config KA KB).mA i' = if i' = i then 1 else 0 := by
  simp [Config.mA, eC_cRow]

theorem eC_mB (j' : Fin KB) :
    (Config.eC i j : Config KA KB).mB j' = if j' = j then 1 else 0 := by
  simp [Config.mB, eC_cCol]

@[simp] theorem eC_t : (Config.eC i j : Config KA KB).t = 1 := by
  simp [Config.t, Config.eC, sum_incC]

@[simp] theorem eC_nA : (Config.eC i j : Config KA KB).nA = 1 := by
  simp [Config.nA, Config.sumA]

@[simp] theorem eC_nB : (Config.eC i j : Config KA KB).nB = 1 := by
  simp [Config.nB, Config.sumB]

theorem eAB_a (i' : Fin KA) : (eAB i j : Config KA KB).a i' = if i' = i then 1 else 0 :=
  incf_zero_apply i i'

theorem eAB_b (j' : Fin KB) : (eAB i j : Config KA KB).b j' = if j' = j then 1 else 0 :=
  incf_zero_apply j j'

@[simp] theorem eAB_c (i' : Fin KA) (j' : Fin KB) : (eAB i j : Config KA KB).c i' j' = 0 := rfl

@[simp] theorem eAB_cRow (i' : Fin KA) : (eAB i j : Config KA KB).cRow i' = 0 := by
  simp [Config.cRow]

@[simp] theorem eAB_cCol (j' : Fin KB) : (eAB i j : Config KA KB).cCol j' = 0 := by
  simp [Config.cCol]

@[simp] theorem eAB_sumA : (eAB i j : Config KA KB).sumA = 1 := by
  simp [Config.sumA, eAB, sum_incf]

@[simp] theorem eAB_sumB : (eAB i j : Config KA KB).sumB = 1 := by
  simp [Config.sumB, eAB, sum_incf]

@[simp] theorem eAB_t : (eAB i j : Config KA KB).t = 0 :=
  Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => rfl

@[simp] theorem eAB_nA : (eAB i j : Config KA KB).nA = 1 := by
  simp [Rhone.LinearAlgebra.Recursion.Config.nA]

@[simp] theorem eAB_nB : (eAB i j : Config KA KB).nB = 1 := by
  simp [Rhone.LinearAlgebra.Recursion.Config.nB]

@[simp] theorem eAB_n : (eAB i j : Config KA KB).n = 2 := by
  simp [Rhone.LinearAlgebra.Recursion.Config.n]

theorem decf_incf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : decf (incf f i) i = f := by
  funext k
  by_cases h : k = i
  · subst h; simp [decf_self, incf_self]
  · simp [decf_of_ne _ h, incf_of_ne _ h]

theorem decC_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    decC (incC m i j) i j = m := by
  funext i' j'
  by_cases h : i' = i
  · subst h
    simp only [decC, incC, Function.update_self, decf_incf]
  · simp [decC, incC, Function.update_of_ne h]

theorem killA_eC : (Config.eC i j : Config KA KB).killA i j = Config.eB j := by
  simp only [Config.killA, Config.eC, Config.eB, decC_incC]

theorem killB_eC : (Config.eC i j : Config KA KB).killB i j = Config.eA i := by
  simp only [Config.killB, Config.eC, Config.eA, decC_incC]

theorem split_eC : (Config.eC i j : Config KA KB).split i j = eAB i j := by
  simp only [Config.split, Config.eC, eAB, decC_incC]

theorem mergeAB_eAB : (eAB i j : Config KA KB).mergeAB i j = Config.eC i j := by
  simp only [Config.mergeAB, eAB, Config.eC, decf_incf]

theorem dropA_eAB : (eAB i j : Config KA KB).dropA i = Config.eB j := by
  simp only [Config.dropA, eAB, Config.eB, decf_incf]

theorem dropB_eAB : (eAB i j : Config KA KB).dropB j = Config.eA i := by
  simp only [Config.dropB, eAB, Config.eA, decf_incf]

end Nat

variable [CommRing F] (θA θB ρ : F) {i : Fin KA} {j : Fin KB}

theorem rhsIA_eC (q : Config KA KB → F) :
    rhsIA θA θB ρ q (Config.eC i j)
      = θA * q (Config.eB j) + θB * q (Config.eA i) + ρ * q (eAB i j) := by
  have h1 : (∑ i', ((Config.eC i j : Config KA KB).coalA i' : F) *
      q ((Config.eC i j : Config KA KB).dropA i')) = 0 :=
    Finset.sum_eq_zero fun i' _ => by simp [Config.coalA]
  have h2 : (∑ j', ((Config.eC i j : Config KA KB).coalB j' : F) *
      q ((Config.eC i j : Config KA KB).dropB j')) = 0 :=
    Finset.sum_eq_zero fun j' _ => by simp [Config.coalB]
  have h3 : (∑ i', ∑ j', ((Config.eC i j : Config KA KB).coalC i' j' : F) *
      q ((Config.eC i j : Config KA KB).dropC i' j')) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => by
      simp only [Config.coalC, eC_c]
      split_ifs <;> simp
  have h4 : (∑ i', ∑ j', ((Config.eC i j : Config KA KB).coalAB i' j' : F) *
      q ((Config.eC i j : Config KA KB).mergeAB i' j')) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => by simp [Config.coalAB]
  have hkA : ∀ i' : Fin KA, (((dropIndA (Config.eC i j : Config KA KB) i' : ℕ) : F) *
        q ((Config.eC i j : Config KA KB).dropA i')
      + ∑ j', ((killIndA (Config.eC i j : Config KA KB) i' j' : ℕ) : F) *
        q ((Config.eC i j : Config KA KB).killA i' j'))
      = if i' = i then q (Config.eB j) else 0 := by
    intro i'
    have hd : dropIndA (Config.eC i j : Config KA KB) i' = 0 := by simp [dropIndA]
    by_cases h : i' = i
    · subst h
      have hin : ∀ j', killIndA (Config.eC i' j : Config KA KB) i' j'
          = if j' = j then 1 else 0 := by
        intro j'
        simp only [killIndA, eC_mA, eC_c]
        by_cases hj : j' = j <;> simp [hj]
      rw [hd]
      rw [Finset.sum_congr rfl fun j' _ =>
        show ((killIndA (Config.eC i' j : Config KA KB) i' j' : ℕ) : F) *
            q ((Config.eC i' j : Config KA KB).killA i' j')
          = if j' = j then q ((Config.eC i' j : Config KA KB).killA i' j') else 0 by
          rw [hin j']; split_ifs <;> simp]
      rw [Finset.sum_ite_eq' Finset.univ j
        (fun j' => q ((Config.eC i' j : Config KA KB).killA i' j')), ite_eq_left (mem_univ j)]
      simp [killA_eC]
    · have hin : ∀ j', killIndA (Config.eC i j : Config KA KB) i' j' = 0 := by
        intro j'
        simp [killIndA, eC_mA, h]
      rw [hd, ite_eq_right h]
      simp [hin]
  have hkB : ∀ j' : Fin KB, (((dropIndB (Config.eC i j : Config KA KB) j' : ℕ) : F) *
        q ((Config.eC i j : Config KA KB).dropB j')
      + ∑ i', ((killIndB (Config.eC i j : Config KA KB) i' j' : ℕ) : F) *
        q ((Config.eC i j : Config KA KB).killB i' j'))
      = if j' = j then q (Config.eA i) else 0 := by
    intro j'
    have hd : dropIndB (Config.eC i j : Config KA KB) j' = 0 := by simp [dropIndB]
    by_cases h : j' = j
    · subst h
      have hin : ∀ i', killIndB (Config.eC i j' : Config KA KB) i' j'
          = if i' = i then 1 else 0 := by
        intro i'
        simp only [killIndB, eC_mB, eC_c]
        by_cases hi : i' = i <;> simp [hi]
      rw [hd]
      rw [Finset.sum_congr rfl fun i' _ =>
        show ((killIndB (Config.eC i j' : Config KA KB) i' j' : ℕ) : F) *
            q ((Config.eC i j' : Config KA KB).killB i' j')
          = if i' = i then q ((Config.eC i j' : Config KA KB).killB i' j') else 0 by
          rw [hin i']; split_ifs <;> simp]
      rw [Finset.sum_ite_eq' Finset.univ i
        (fun i' => q ((Config.eC i j' : Config KA KB).killB i' j')), ite_eq_left (mem_univ i)]
      simp [killB_eC]
    · have hin : ∀ i', killIndB (Config.eC i j : Config KA KB) i' j' = 0 := by
        intro i'
        simp [killIndB, eC_mB, h]
      rw [hd, ite_eq_right h]
      simp [hin]
  have h7 : (∑ i', ∑ j', (((Config.eC i j : Config KA KB).c i' j' : ℕ) : F) *
      q ((Config.eC i j : Config KA KB).split i' j')) = q (eAB i j) := by
    rw [Finset.sum_congr rfl fun i' _ =>
      show (∑ j', (((Config.eC i j : Config KA KB).c i' j' : ℕ) : F) *
          q ((Config.eC i j : Config KA KB).split i' j'))
        = if i' = i then q (eAB i j) else 0 by
        by_cases h : i' = i
        · subst h
          rw [Finset.sum_congr rfl fun j' _ =>
            show (((Config.eC i' j : Config KA KB).c i' j' : ℕ) : F) *
                q ((Config.eC i' j : Config KA KB).split i' j')
              = if j' = j then q ((Config.eC i' j : Config KA KB).split i' j') else 0 by
              rw [eC_c, ite_eq_left rfl]; split_ifs <;> simp]
          rw [Finset.sum_ite_eq' Finset.univ j
            (fun j' => q ((Config.eC i' j : Config KA KB).split i' j')), ite_eq_left (mem_univ j)]
          simp [split_eC]
        · rw [ite_eq_right h]
          exact Finset.sum_eq_zero fun j' _ => by rw [eC_c, ite_eq_right h]; simp]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ : Fin KA => q (eAB i j)), ite_eq_left (mem_univ i)]
  simp only [rhsIA, h1, h2, h3, h4, h7, zero_add, add_zero]
  rw [Finset.sum_congr rfl fun i' _ => hkA i', Finset.sum_congr rfl fun j' _ => hkB j']
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ : Fin KA => q (Config.eB j)),
    ite_eq_left (mem_univ i),
    Finset.sum_ite_eq' Finset.univ j (fun _ : Fin KB => q (Config.eA i)), ite_eq_left (mem_univ j)]

theorem rhsIA_eAB (q : Config KA KB → F) :
    rhsIA θA θB ρ q (eAB i j)
      = 2 * q (Config.eC i j) + θA * q (Config.eB j) + θB * q (Config.eA i) := by
  have h1 : (∑ i', ((eAB i j : Config KA KB).coalA i' : F) *
      q ((eAB i j : Config KA KB).dropA i')) = 0 :=
    Finset.sum_eq_zero fun i' _ => by
      simp only [Config.coalA, eAB_a, eAB_cRow]
      split_ifs <;> simp
  have h2 : (∑ j', ((eAB i j : Config KA KB).coalB j' : F) *
      q ((eAB i j : Config KA KB).dropB j')) = 0 :=
    Finset.sum_eq_zero fun j' _ => by
      simp only [Config.coalB, eAB_b, eAB_cCol]
      split_ifs <;> simp
  have h3 : (∑ i', ∑ j', ((eAB i j : Config KA KB).coalC i' j' : F) *
      q ((eAB i j : Config KA KB).dropC i' j')) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => by simp [Config.coalC]
  have h4 : (∑ i', ∑ j', (((eAB i j : Config KA KB).coalAB i' j' : ℕ) : F) *
      q ((eAB i j : Config KA KB).mergeAB i' j')) = 2 * q (Config.eC i j) := by
    rw [Finset.sum_congr rfl fun i' _ =>
      show (∑ j', (((eAB i j : Config KA KB).coalAB i' j' : ℕ) : F) *
          q ((eAB i j : Config KA KB).mergeAB i' j'))
        = if i' = i then 2 * q (Config.eC i j) else 0 by
        by_cases h : i' = i
        · subst h
          rw [Finset.sum_congr rfl fun j' _ =>
            show (((eAB i' j : Config KA KB).coalAB i' j' : ℕ) : F) *
                q ((eAB i' j : Config KA KB).mergeAB i' j')
              = if j' = j then 2 * q ((eAB i' j : Config KA KB).mergeAB i' j') else 0 by
              simp only [Config.coalAB, eAB_a, eAB_b]
              split_ifs <;> simp]
          rw [Finset.sum_ite_eq' Finset.univ j
            (fun j' => 2 * q ((eAB i' j : Config KA KB).mergeAB i' j')), ite_eq_left (mem_univ j)]
          simp [mergeAB_eAB]
        · rw [ite_eq_right h]
          exact Finset.sum_eq_zero fun j' _ => by
            simp only [Config.coalAB, eAB_a, ite_eq_right h]; simp]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ : Fin KA => 2 * q (Config.eC i j)),
      ite_eq_left (mem_univ i)]
  have hkA : ∀ i' : Fin KA, (((dropIndA (eAB i j : Config KA KB) i' : ℕ) : F) *
        q ((eAB i j : Config KA KB).dropA i')
      + ∑ j', ((killIndA (eAB i j : Config KA KB) i' j' : ℕ) : F) *
        q ((eAB i j : Config KA KB).killA i' j'))
      = if i' = i then q (Config.eB j) else 0 := by
    intro i'
    have hin : ∀ j', killIndA (eAB i j : Config KA KB) i' j' = 0 := fun j' => by
      simp [killIndA]
    by_cases h : i' = i
    · subst h
      have hd : dropIndA (eAB i' j : Config KA KB) i' = 1 := by
        simp [dropIndA, eAB_a]
      rw [hd, ite_eq_left rfl, dropA_eAB]
      simp [hin]
    · have hd : dropIndA (eAB i j : Config KA KB) i' = 0 := by
        simp [dropIndA, eAB_a, h]
      rw [hd, ite_eq_right h]
      simp [hin]
  have hkB : ∀ j' : Fin KB, (((dropIndB (eAB i j : Config KA KB) j' : ℕ) : F) *
        q ((eAB i j : Config KA KB).dropB j')
      + ∑ i', ((killIndB (eAB i j : Config KA KB) i' j' : ℕ) : F) *
        q ((eAB i j : Config KA KB).killB i' j'))
      = if j' = j then q (Config.eA i) else 0 := by
    intro j'
    have hin : ∀ i', killIndB (eAB i j : Config KA KB) i' j' = 0 := fun i' => by
      simp [killIndB]
    by_cases h : j' = j
    · subst h
      have hd : dropIndB (eAB i j' : Config KA KB) j' = 1 := by
        simp [dropIndB, eAB_b]
      rw [hd, ite_eq_left rfl, dropB_eAB]
      simp [hin]
    · have hd : dropIndB (eAB i j : Config KA KB) j' = 0 := by
        simp [dropIndB, eAB_b, h]
      rw [hd, ite_eq_right h]
      simp [hin]
  have h7 : (∑ i', ∑ j', (((eAB i j : Config KA KB).c i' j' : ℕ) : F) *
      q ((eAB i j : Config KA KB).split i' j')) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => by simp
  simp only [rhsIA, h1, h2, h3, h4, h7, zero_add, add_zero, mul_zero]
  rw [Finset.sum_congr rfl fun i' _ => hkA i', Finset.sum_congr rfl fun j' _ => hkB j']
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ : Fin KA => q (Config.eB j)),
    ite_eq_left (mem_univ i),
    Finset.sum_ite_eq' Finset.univ j (fun _ : Fin KB => q (Config.eA i)), ite_eq_left (mem_univ j)]

section Solve

variable {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G] {tA tB r : G}

theorem diag_eC (i : Fin KA) (j : Fin KB) :
    diag tA tB r (Config.eC i j : Config KA KB) = tA + tB + r := by
  simp [Rhone.LinearAlgebra.Recursion.diag]

theorem diag_eAB (i : Fin KA) (j : Fin KB) :
    diag tA tB r (eAB i j : Config KA KB) = 2 + tA + tB := by
  simp [Rhone.LinearAlgebra.Recursion.diag]

theorem eC_eq_one (htA : 0 < tA) (htB : 0 < tB) (hr : 0 ≤ r) {q : Config KA KB → G}
    (h : IsSolutionIA tA tB r q) (i : Fin KA) (j : Fin KB) : q (Config.eC i j) = 1 := by
  have e1 := h.recursion (Config.eC i j) (by simp)
  rw [diag_eC, rhsIA_eC, h.bdryA, h.bdryB] at e1
  have e2 := h.recursion (eAB i j) (by simp)
  rw [diag_eAB, rhsIA_eAB, h.bdryA, h.bdryB] at e2
  have hs : (0 : G) < tA + tB := by linarith
  have hs2 : (0 : G) < 2 + tA + tB + r := by linarith
  have key : ((tA + tB) * (2 + tA + tB + r)) * q (Config.eC i j)
      = ((tA + tB) * (2 + tA + tB + r)) * 1 := by
    linear_combination (2 + tA + tB) * e1 + r * e2
  exact mul_left_cancel₀ (ne_of_gt (mul_pos hs hs2)) key

theorem eAB_eq_one (htA : 0 < tA) (htB : 0 < tB) (hr : 0 ≤ r) {q : Config KA KB → G}
    (h : IsSolutionIA tA tB r q) (i : Fin KA) (j : Fin KB) : q (eAB i j) = 1 := by
  have e2 := h.recursion (eAB i j) (by simp)
  rw [diag_eAB, rhsIA_eAB, h.bdryA, h.bdryB, eC_eq_one htA htB hr h i j] at e2
  have hs : (0 : G) < 2 + tA + tB := by linarith
  have key : (2 + tA + tB) * q (eAB i j) = (2 + tA + tB) * 1 := by linear_combination e2
  exact mul_left_cancel₀ (ne_of_gt hs) key

theorem PIA_eC (htA : 0 < tA) (htB : 0 < tB) (hr : 0 ≤ r) (i : Fin KA) (j : Fin KB) :
    PIA (KA := KA) (KB := KB) htA htB hr (Config.eC i j) = 1 :=
  eC_eq_one htA htB hr (PIA_isSolutionIA htA htB hr) i j

end Solve

end Rhone.Probability.InfiniteAlleles
