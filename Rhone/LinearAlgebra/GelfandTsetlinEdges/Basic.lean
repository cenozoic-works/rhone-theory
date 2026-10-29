/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GelfandTsetlinEdges.Defs

/-! # Gelfand–Tsetlin raising and lowering laws in cleared form, and their normalization -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

open Finset

variable {F : Type*} [Field F] {n : ℕ} {x y z : Fin (n + 1) → F} {r : Fin (n + 1)}

theorem prodD_ne_zero (hz : ∀ s ≠ r, z s - z r ≠ 0) :
    ∏ s ∈ univ.erase r, (z s - z r) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun s hs => hz s (Finset.ne_of_mem_erase hs)

theorem prodDm_ne_zero (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    ∏ s ∈ univ.erase r, (z s - z r - 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun s hs => hz' s (Finset.ne_of_mem_erase hs)

theorem prodDm_erase_eq_neg (z : Fin (n + 1) → F) (r : Fin (n + 1)) :
    ∏ s ∈ univ.erase r, (z s - z r - 1) = -∏ s, (z s - z r - 1) := by
  have h := Finset.mul_prod_erase univ (fun s => z s - z r - 1) (mem_univ r)
  simp only [sub_self, zero_sub] at h
  linear_combination -h

theorem prodN_ne_zero (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    (∏ j : Fin n, (z j.castSucc - z r - 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  by_cases h : (j.castSucc : Fin (n + 1)) = r
  · rw [h]; norm_num
  · exact hz' _ h

theorem glast_ne_zero (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    z (Fin.last n) - z r - 1 ≠ 0 := by
  by_cases h : (Fin.last n : Fin (n + 1)) = r
  · rw [h]; norm_num
  · exact hz' _ h

theorem gt_raise_eq_beta_form (x z : Fin (n + 1) → F) (r : Fin (n + 1)) :
    Aup x z r = (z r + 1) * Glaw x z r := by
  unfold Aup Glaw
  ring

theorem gt_raise_cleared (hz : ∀ s ≠ r, z s - z r ≠ 0) :
    (∏ s ∈ univ.erase r, (z s - z r)) * Aup x z r = (z r + 1) * ∏ s, (x s - z r) := by
  have hD := prodD_ne_zero hz
  rw [gt_raise_eq_beta_form, Glaw]
  field_simp

theorem gt_lower_closed_form (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    Adown z r = -1 / (z (Fin.last n) - z r - 1) := by
  have hN := prodN_ne_zero hz'
  have hgl := glast_ne_zero hz'
  unfold Adown
  rw [prodDm_erase_eq_neg, Fin.prod_univ_castSucc]
  field_simp

theorem gt_lower_closed_form_if (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    Adown z r = if r = Fin.last n then 1 else -1 / (z (Fin.last n) - z r - 1) := by
  rw [gt_lower_closed_form hz']
  split_ifs with h
  · rw [h]; norm_num
  · rfl

theorem Adown_ne_zero (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) : Adown z r ≠ 0 := by
  rw [gt_lower_closed_form hz']
  exact div_ne_zero (by norm_num) (glast_ne_zero hz')

theorem G_gauge_one (hz : ∀ s ≠ r, z s - z r ≠ 0) : Glaw (eAdd z r) z r = 1 := by
  have hD := prodD_ne_zero hz
  have h1 : ∀ s ∈ univ.erase r, (eAdd z r s - z r) = z s - z r := fun s hs => by
    rw [eAdd, Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  rw [Glaw, ← Finset.mul_prod_erase univ (fun s => eAdd z r s - z r) (mem_univ r),
    Finset.prod_congr rfl h1, eAdd, Function.update_self]
  field_simp
  ring

theorem Aup_gauge (hz : ∀ s ≠ r, z s - z r ≠ 0) : Aup (eAdd z r) z r = z r + 1 := by
  rw [gt_raise_eq_beta_form, G_gauge_one hz, mul_one]

theorem gauge_ratio_cleared (hz : ∀ s ≠ r, z s - z r ≠ 0) :
    Aup x z r * Adown z r = Glaw x z r * (Aup (eAdd z r) z r * Adown z r) := by
  rw [Aup_gauge hz, gt_raise_eq_beta_form]
  ring

theorem gauge_ratio_eq_law (hz : ∀ s ≠ r, z s - z r ≠ 0) (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0)
    (hz0 : z r + 1 ≠ 0) :
    Aup x z r * Adown z r / (Aup (eAdd z r) z r * Adown z r) = Glaw x z r := by
  have hAd := Adown_ne_zero hz'
  rw [Aup_gauge hz, gt_raise_eq_beta_form]
  field_simp

theorem gauge_ratio_nonvacuous (hz : ∀ s ≠ r, z s - z r ≠ 0) (hz0 : z r + 1 ≠ 0)
    (hG : Glaw x z r ≠ 0) {w : F}
    (h : Aup x z r * Adown z r = Glaw x z r * (Aup (eAdd z r) z r * w)) :
    w = Adown z r := by
  rw [Aup_gauge hz, gt_raise_eq_beta_form] at h
  have h' : Glaw x z r * (z r + 1) * (Adown z r - w) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' (mul_ne_zero hG hz0)
  · exact (sub_eq_zero.mp h'').symm

theorem sector_law_of_G (hz : ∀ s ≠ r, z s - z r ≠ 0) (hz' : ∀ s ≠ r, z s - z r - 1 ≠ 0) :
    cBeta z r * Glaw x z r * Glaw y z r = sectorLaw x y z r := by
  have hD := prodD_ne_zero hz
  have hDm := prodDm_ne_zero hz'
  unfold cBeta Glaw sectorLaw
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  field_simp

end Rhone.LinearAlgebra.GelfandTsetlinEdges
