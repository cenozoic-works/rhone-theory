/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GelfandTsetlinEdges.Basic

/-! # The two-element box: `κ(λ₀, μ₀, ν) = b₁ + ε − b_r`, and the constant -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

open Finset

variable {F : Type*} [Field F] {n : ℕ} {z : Fin (n + 1) → F} {r : Fin (n + 1)} {ε : F}

theorem sizeB_eq (b : Fin (n + 1) → F) : sizeB b = (∑ s, b s) - offSum F n := by
  rw [sizeB, offSum, Finset.sum_sub_distrib]

theorem offSum_mul_two (n : ℕ) : offSum F n * 2 = ((n : F) + 1) * (n : F) := by
  have h := Finset.sum_range_id_mul_two (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have hg : (∑ i ∈ Finset.range (n + 1), (i : F)) * 2 = ((n : F) + 1) * (n : F) := by
    have h' := congrArg (fun k : ℕ => (k : F)) h
    push_cast at h'
    exact h'
  rw [offSum, Fin.sum_univ_eq_sum_range (fun i => (n : F) - (i : F)) (n + 1),
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linear_combination -hg

theorem sum_update_comp (φ : F → F) (f : Fin (n + 1) → F) (r : Fin (n + 1)) (v : F) :
    ∑ s, φ (Function.update f r v s) = (∑ s, φ (f s)) + (φ v - φ (f r)) := by
  have h1 : ∑ s, φ (Function.update f r v s) = φ v + ∑ s ∈ univ.erase r, φ (f s) := by
    rw [← Finset.add_sum_erase univ (fun s => φ (Function.update f r v s)) (mem_univ r),
      Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun s hs => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have h2 : ∑ s, φ (f s) = φ (f r) + ∑ s ∈ univ.erase r, φ (f s) :=
    (Finset.add_sum_erase univ (fun s => φ (f s)) (mem_univ r)).symm
  rw [h1, h2]; ring

theorem sum_eAdd (z : Fin (n + 1) → F) (r : Fin (n + 1)) :
    ∑ s, eAdd z r s = (∑ s, z s) + 1 := by
  have h := sum_update_comp (fun t : F => t) z r (z r + 1)
  simp only [eAdd]
  rw [h]
  ring

theorem sum_sq_eAdd (z : Fin (n + 1) → F) (r : Fin (n + 1)) :
    ∑ s, eAdd z r s ^ 2 = (∑ s, z s ^ 2) + (2 * z r + 1) := by
  rw [eAdd, sum_update_comp (fun t => t ^ 2) z r (z r + 1)]
  ring

theorem sum_castSucc (z : Fin (n + 1) → F) :
    ∑ j : Fin n, z j.castSucc = (∑ s, z s) - z (Fin.last n) := by
  rw [Fin.sum_univ_castSucc (f := z)]; ring

theorem sum_sq_castSucc (z : Fin (n + 1) → F) :
    ∑ j : Fin n, z j.castSucc ^ 2 = (∑ s, z s ^ 2) - z (Fin.last n) ^ 2 := by
  rw [Fin.sum_univ_castSucc (f := fun s => z s ^ 2)]; ring

theorem sum_bMu0 (z : Fin (n + 1) → F) (ε : F) :
    ∑ s, bMu0 z ε s = (z 0 + ε) + ((∑ s, z s) - z (Fin.last n)) - (n : F) := by
  rw [Fin.sum_univ_succ (f := bMu0 z ε)]
  simp only [bMu0, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_castSucc]
  ring

theorem sum_sq_bMu0 (z : Fin (n + 1) → F) (ε : F) :
    ∑ s, bMu0 z ε s ^ 2 = (z 0 + ε) ^ 2 + ((∑ s, z s ^ 2) - z (Fin.last n) ^ 2)
      - 2 * ((∑ s, z s) - z (Fin.last n)) + (n : F) := by
  rw [Fin.sum_univ_succ (f := fun s => bMu0 z ε s ^ 2)]
  simp only [bMu0, Fin.cons_zero, Fin.cons_succ]
  have h : ∀ j : Fin n, (z j.castSucc - 1) ^ 2 = z j.castSucc ^ 2 - 2 * z j.castSucc + 1 :=
    fun j => by ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sum_castSucc, sum_sq_castSucc]
  ring

theorem hz0_of_padding (hlast : z (Fin.last n) = 0) (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    z r + 1 ≠ 0 := by
  have h := glast_ne_zero hz'
  rw [hlast] at h
  intro hc
  exact h (by linear_combination -hc)

theorem prod_bMu0 (z : Fin (n + 1) → F) (r : Fin (n + 1)) (ε : F) :
    ∏ s, (bMu0 z ε s - z r) =
      (z 0 + ε - z r) * ∏ j : Fin n, (z j.castSucc - z r - 1) := by
  rw [Fin.prod_univ_succ (f := fun s => bMu0 z ε s - z r)]
  simp only [bMu0, Fin.cons_zero, Fin.cons_succ]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by ring

theorem cBeta_mul_Glaw_bMu0 (hlast : z (Fin.last n) = 0) (hz : ∀ s ≠ r, z s - z r ≠ 0)
    (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    cBeta z r * Glaw (bMu0 z ε) z r = z 0 + ε - z r := by
  have hD := prodD_ne_zero hz
  have hN := prodN_ne_zero hz'
  have hz0 := hz0_of_padding hlast hz'
  have hDm : ∏ s ∈ univ.erase r, (z s - z r - 1)
      = (∏ j : Fin n, (z j.castSucc - z r - 1)) * (z r + 1) := by
    rw [prodDm_erase_eq_neg, Fin.prod_univ_castSucc (f := fun s => z s - z r - 1), hlast]
    ring
  rw [cBeta, Glaw, Finset.prod_div_distrib, prod_bMu0, hDm]
  field_simp

section CharZeroField

variable [CharZero F]

theorem kappa_two_element_box (hlast : z (Fin.last n) = 0) :
    kappaB (eAdd z r) (bMu0 z ε) z = z 0 + ε - z r := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hP : offSum F n = (((n : F) + 1) * (n : F)) / 2 := by
    rw [eq_div_iff h2]
    exact offSum_mul_two n
  rw [kappaB, mB, CB, CB, CB, sizeB_eq, sizeB_eq, sizeB_eq, sum_eAdd, sum_sq_eAdd, sum_bMu0,
    sum_sq_bMu0, hlast, hP]
  field_simp
  ring

theorem constant_derivation (hlast : z (Fin.last n) = 0) (hz : ∀ s ≠ r, z s - z r ≠ 0)
    (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    kappaB (eAdd z r) (bMu0 z ε) z
      = cBeta z r * Glaw (eAdd z r) z r * Glaw (bMu0 z ε) z r := by
  rw [G_gauge_one hz, mul_one, cBeta_mul_Glaw_bMu0 hlast hz hz', kappa_two_element_box hlast]

theorem cBeta_eq_kappa_div (hlast : z (Fin.last n) = 0) (hz : ∀ s ≠ r, z s - z r ≠ 0)
    (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) (hne : z 0 + ε - z r ≠ 0) :
    cBeta z r
      = kappaB (eAdd z r) (bMu0 z ε) z / (Glaw (eAdd z r) z r * Glaw (bMu0 z ε) z r) := by
  have hmul := cBeta_mul_Glaw_bMu0 (ε := ε) hlast hz hz'
  have hG : Glaw (bMu0 z ε) z r ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hmul
    exact hne hmul.symm
  rw [G_gauge_one hz, one_mul, kappa_two_element_box hlast, eq_div_iff hG]
  exact hmul

end CharZeroField

end Rhone.LinearAlgebra.GelfandTsetlinEdges
