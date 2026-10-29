/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.RhoZero

/-! # Failure of the parent-independent-mutation closed form under general mutation -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

section OneAlphabet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {ν : ι → F} {P : ι → ι → F}

def qOneI (θ : F) (ν : ι → F) (m : ι → ℕ) : F :=
  (∏ x, rising (θ * ν x) (m x)) / rising θ (∑ x, m x)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prod_rising_incfI (f : ι → F) (m : ι → ℕ) (z : ι) :
    ∏ x, rising (f x) (incf m z x) = (∏ x, rising (f x) (m x)) * (f z + ((m z : ℕ) : F)) := by
  have hsplit : ∀ g : ι → ℕ, (∏ x, rising (f x) (g x))
      = rising (f z) (g z) * ∏ x ∈ Finset.univ.erase z, rising (f x) (g x) :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ z)).symm
  have herase : ∀ x ∈ Finset.univ.erase z, rising (f x) (incf m z x) = rising (f x) (m x) := by
    intro x hx
    rw [incf_of_ne _ (Finset.mem_erase.mp hx).1]
  rw [hsplit (incf m z), hsplit m, Finset.prod_congr rfl herase, incf_self, rising_succ]
  ring

def pairf (z w : ι) : ι → ℕ := incf (incf (fun _ => 0) z) w

theorem sum_pairf (z w : ι) : ∑ x, pairf z w x = 2 := by
  rw [pairf, sum_incf, sum_incf]
  simp

omit [Fintype ι] in
theorem decf_pairf_self (z : ι) : decf (pairf z z) z = incf (fun _ => 0) z := by
  rw [pairf, Probability.Denominator.decf_incf_self]

omit [Fintype ι] in
theorem pairf_apply_self (z : ι) : pairf z z z = 2 := by
  rw [pairf, incf_self, incf_self]

omit [Fintype ι] in
theorem pairf_apply_of_ne {z x : ι} (h : x ≠ z) : pairf z z x = 0 := by
  rw [pairf, incf_of_ne _ h, incf_of_ne _ h]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem qOneI_single (hθ : θ ≠ 0) (z : ι) : qOneI θ ν (incf (fun _ => 0) z) = ν z := by
  have h1 : ∑ x, incf (fun _ => (0 : ℕ)) z x = 1 := by rw [sum_incf]; simp
  have h2 : ∏ x, rising (θ * ν x) (incf (fun _ => 0) z x) = θ * ν z := by
    rw [prod_rising_incfI]
    simp
  rw [qOneI, h1, h2, rising_one]
  field_simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem qOneI_pairf (hθ : θ ≠ 0) (hθ1 : θ + 1 ≠ 0) (z w : ι) :
    qOneI θ ν (pairf z w) * (θ * (θ + 1))
      = (θ * ν z) * (θ * ν w + (if w = z then 1 else 0)) := by
  have hsum := sum_pairf z w
  have hprod : ∏ x, rising (θ * ν x) (pairf z w x)
      = (θ * ν z) * (θ * ν w + ((incf (fun _ => (0 : ℕ)) z w : ℕ) : F)) := by
    rw [pairf, prod_rising_incfI]
    congr 1
    rw [prod_rising_incfI]
    simp
  have hcast : ((incf (fun _ => (0 : ℕ)) z w : ℕ) : F) = if w = z then 1 else 0 := by
    rw [Probability.Denominator.incf_apply]
    split_ifs <;> simp
  have hr : rising θ (∑ x, pairf z w x) = θ * (θ + 1) := by
    rw [hsum, rising_succ, rising_one]
    push_cast
    ring
  rw [qOneI, hprod, hcast, hr]
  field_simp

theorem qOneI_defect (hθ : 0 < θ) (hst : ∀ x, ∑ y, ν y * P y x = ν x) (x₀ : ι) :
    ((((∑ z, pairf x₀ x₀ z) * ((∑ z, pairf x₀ x₀ z) - 1) : ℕ) : F)
        + θ * ((∑ z, pairf x₀ x₀ z : ℕ) : F)) * qOneI θ ν (pairf x₀ x₀)
      - ((∑ z, ((pairf x₀ x₀ z * (pairf x₀ x₀ z - 1) : ℕ) : F)
            * qOneI θ ν (decf (pairf x₀ x₀) z))
          + θ * ∑ z, ∑ y, P y z * ((pairf x₀ x₀ z : ℕ) : F)
              * qOneI θ ν (incf (decf (pairf x₀ x₀) z) y))
      = 2 * θ * ν x₀ * (ν x₀ - P x₀ x₀) / (θ + 1) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθ1 : θ + 1 ≠ 0 := by positivity
  have hsum := sum_pairf x₀ x₀
  have hval : qOneI θ ν (pairf x₀ x₀) * (θ * (θ + 1)) = (θ * ν x₀) * (θ * ν x₀ + 1) := by
    rw [qOneI_pairf hθ0 hθ1]
    simp
  have hcoal : (∑ z, ((pairf x₀ x₀ z * (pairf x₀ x₀ z - 1) : ℕ) : F)
      * qOneI θ ν (decf (pairf x₀ x₀) z)) = 2 * ν x₀ := by
    rw [Finset.sum_eq_single_of_mem x₀ (Finset.mem_univ x₀)]
    · rw [pairf_apply_self, decf_pairf_self, qOneI_single hθ0]
      push_cast
      ring
    · intro z _ hz
      rw [pairf_apply_of_ne hz]
      simp
  have hmut : (∑ z, ∑ y, P y z * ((pairf x₀ x₀ z : ℕ) : F)
      * qOneI θ ν (incf (decf (pairf x₀ x₀) z) y)) * (θ * (θ + 1))
      = 2 * (θ * ν x₀) * (θ * ν x₀ + P x₀ x₀) := by
    rw [Finset.sum_eq_single_of_mem x₀ (Finset.mem_univ x₀)]
    · rw [pairf_apply_self, decf_pairf_self]
      have hval2 : ∀ y : ι, qOneI θ ν (incf (incf (fun _ => 0) x₀) y) * (θ * (θ + 1))
          = (θ * ν x₀) * (θ * ν y + (if y = x₀ then 1 else 0)) := fun y => qOneI_pairf hθ0 hθ1 x₀ y
      rw [Finset.sum_mul]
      have hstep : ∀ y : ι, P y x₀ * ((2 : ℕ) : F)
            * qOneI θ ν (incf (incf (fun _ => 0) x₀) y) * (θ * (θ + 1))
          = 2 * (θ * ν x₀) * (P y x₀ * (θ * ν y) + P y x₀ * (if y = x₀ then 1 else 0)) := by
        intro y
        have hy := hval2 y
        push_cast
        linear_combination (2 * P y x₀) * hy
      rw [Finset.sum_congr rfl fun y _ => hstep y, ← Finset.mul_sum, Finset.sum_add_distrib]
      have h1 : (∑ y, P y x₀ * (θ * ν y)) = θ * ν x₀ := by
        have : (∑ y, P y x₀ * (θ * ν y)) = θ * ∑ y, ν y * P y x₀ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [this, hst x₀]
      have h2 : (∑ y, P y x₀ * (if y = x₀ then 1 else 0)) = P x₀ x₀ := by
        rw [Finset.sum_eq_single_of_mem x₀ (Finset.mem_univ x₀)]
        · simp
        · intro y _ hy; simp [hy]
      rw [h1, h2]
    · intro z _ hz
      rw [pairf_apply_of_ne hz]
      exact Finset.sum_eq_zero fun y _ => by simp
  have hden : θ * (θ + 1) ≠ 0 := by positivity
  have hQ : qOneI θ ν (pairf x₀ x₀) = (θ * ν x₀) * (θ * ν x₀ + 1) / (θ * (θ + 1)) :=
    eq_div_of_mul_eq hden hval
  have hS : (∑ z, ∑ y, P y z * ((pairf x₀ x₀ z : ℕ) : F)
      * qOneI θ ν (incf (decf (pairf x₀ x₀) z) y))
      = 2 * (θ * ν x₀) * (θ * ν x₀ + P x₀ x₀) / (θ * (θ + 1)) :=
    eq_div_of_mul_eq hden hmut
  rw [hsum, hcoal, hQ, hS]
  push_cast
  field_simp
  ring

theorem not_isSolutionOneG_qOneI (hθ : 0 < θ) (hν : ∀ x, 0 < ν x)
    (hst : ∀ x, ∑ y, ν y * P y x = ν x) {x₀ : ι} (hne : P x₀ x₀ ≠ ν x₀) :
    ¬ IsSolutionOneG θ ν P (qOneI θ ν) := by
  intro hsol
  have hνx := hν x₀
  have hθ1 : (θ : F) + 1 ≠ 0 := by positivity
  have hrec := hsol.recursion (pairf x₀ x₀) (by rw [sum_pairf])
  have hd := qOneI_defect (ν := ν) (P := P) hθ hst x₀
  rw [hrec, sub_self] at hd
  rcases div_eq_zero_iff.mp hd.symm with h | h
  · have hne0 : (2 : F) * θ * ν x₀ ≠ 0 := by positivity
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hne0
    · exact hne (by linarith [h'])
  · exact absurd h hθ1

end OneAlphabet

section Product

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB : F} {νA : Fin KA → F} {νB : Fin KB → F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prodMat_pim_diag (i : Fin KA) (j : Fin KB) :
    prodMat θA θB (pimMat νA) (pimMat νB) (i, j) (i, j)
      = (θA * νA i + θB * νB j) / (θA + θB) := by
  simp [prodMat, pimMat]

theorem lt_one_of_nontrivial {ι : Type*} [Fintype ι] [Nontrivial ι] {w : ι → F}
    (hpos : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) (x : ι) : w x < 1 := by
  classical
  obtain ⟨y, hy⟩ := exists_ne x
  have hpair : w x + w y ≤ ∑ z, w z := by
    have hsub : ({x, y} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => (hpos z).le)
    rwa [Finset.sum_pair (Ne.symm hy)] at this
  have := hpos y
  linarith [hsum ▸ hpair]

theorem prodMat_not_constRows [Nontrivial (Fin KA)] [Nontrivial (Fin KB)]
    (hθA : 0 < θA) (hθB : 0 < θB) (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j) :
    ¬ ∃ w : Fin KA × Fin KB → F,
      prodMat θA θB (pimMat νA) (pimMat νB) = fun _ x => w x := by
  rintro ⟨w, hw⟩
  obtain ⟨i, j⟩ : Fin KA × Fin KB := ⟨Classical.arbitrary _, Classical.arbitrary _⟩
  obtain ⟨i', hi'⟩ := exists_ne i
  obtain ⟨j', hj'⟩ := exists_ne j
  have hs : θA + θB ≠ 0 := by positivity
  have h1 : prodMat θA θB (pimMat νA) (pimMat νB) (i, j) (i, j) = w (i, j) := by
    rw [hw]
  have h2 : prodMat θA θB (pimMat νA) (pimMat νB) (i', j') (i, j) = w (i, j) := by
    rw [hw]
  rw [prodMat_pim_diag] at h1
  have h2' : prodMat θA θB (pimMat νA) (pimMat νB) (i', j') (i, j) = 0 := by
    simp [prodMat, hi', hj']
  rw [h2'] at h2
  have h3 : θA * νA i + θB * νB j = 0 := by
    have := h1.trans h2.symm
    field_simp at this
    linarith [this]
  nlinarith [hνA i, hνB j, hθA, hθB]

theorem no_pim_closed_form [Nontrivial (Fin KA)] [Nontrivial (Fin KB)]
    (hθA : 0 < θA) (hθB : 0 < θB) (hνApos : ∀ i, 0 < νA i) (hνBpos : ∀ j, 0 < νB j)
    (hνA : ∑ i, νA i = 1) (hνB : ∑ j, νB j = 1) :
    ¬ IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB (pimMat νA) (pimMat νB))
      (qOneI (θA + θB) (prodNu νA νB)) := by
  have hs : (0 : F) < θA + θB := by linarith
  obtain ⟨i, j⟩ : Fin KA × Fin KB := ⟨Classical.arbitrary _, Classical.arbitrary _⟩
  refine not_isSolutionOneG_qOneI (x₀ := (i, j)) hs (prodNu_pos hνApos hνBpos)
    (prodMat_stationary hs.ne' (stationary_pimMat hνA) (stationary_pimMat hνB)) ?_
  rw [prodMat_pim_diag, prodNu]
  have hA1 : νA i < 1 := lt_one_of_nontrivial hνApos hνA i
  have hB1 : νB j < 1 := lt_one_of_nontrivial hνBpos hνB j
  have hpos : 0 < θA * νA i * (1 - νB j) + θB * νB j * (1 - νA i) := by
    have h1 : 0 < θA * νA i * (1 - νB j) :=
      mul_pos (mul_pos hθA (hνApos i)) (by linarith)
    have h2 : 0 < θB * νB j * (1 - νA i) :=
      mul_pos (mul_pos hθB (hνBpos j)) (by linarith)
    linarith
  intro heq
  rw [div_eq_iff hs.ne'] at heq
  nlinarith [heq, hpos]

end Product

end Rhone.MarkovChain.GeneralMutation
