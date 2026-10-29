/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.Strings
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Module.BigOperators

/-! # The explicit projector onto the primitive components -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset
open scoped Nat

variable {F : Type*} [Field F] {i : ℕ}

def projCoef (F : Type*) [Field F] (M l : ℕ) : F :=
  (-1) ^ l * ((M + 1)! : F) / ((l ! : F) * ((M + l + 1)! : F))

def proj (k t : ℕ) : Module.End F (Finset (Fin i) → F) :=
  (((i - 2 * k - (t - k))! : F) / (((t - k)! : F) * ((i - 2 * k)! : F))) •
    ∑ l ∈ range (k + 1), projCoef F (i - 2 * k) l • (D ^ l * U ^ (l + (t - k)))

theorem proj_apply (k t : ℕ) (x : Finset (Fin i) → F) :
    proj k t x = (((i - 2 * k - (t - k))! : F) / (((t - k)! : F) * ((i - 2 * k)! : F))) •
      ∑ l ∈ range (k + 1), projCoef F (i - 2 * k) l • (D ^ l) ((U ^ (l + (t - k))) x) := by
  simp [proj, LinearMap.sum_apply]

section CharZero

variable [CharZero F]

theorem projCoef_succ (M l : ℕ) :
    projCoef F M (l + 1) * (((l : F) + 1) * ((M : F) + (l : F) + 2)) = -projCoef F M l := by
  have h1 : ((l ! : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  have h2 : (((M + l + 1)! : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (l : F) + 1 ≠ 0 := Nat.cast_add_one_ne_zero l
  have h4 : (M : F) + (l : F) + 2 ≠ 0 := by
    have : ((M + l + 2 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using this
  have h5 : (2 : F) + (M : F) + (l : F) ≠ 0 := by
    rwa [show (2 : F) + (M : F) + (l : F) = (M : F) + (l : F) + 2 from by ring]
  have h6 : (M : F) + (l : F) + 1 + 1 ≠ 0 := by
    rwa [show (M : F) + (l : F) + 1 + 1 = (M : F) + (l : F) + 2 from by ring]
  rw [projCoef, projCoef, show M + (l + 1) + 1 = (M + l + 1) + 1 from by omega,
    Nat.factorial_succ l, Nat.factorial_succ (M + l + 1)]
  push_cast
  field_simp
  ring

theorem U_proj {k t : ℕ} (hkt : k ≤ t) (hk : 2 * k ≤ i) {x : Finset (Fin i) → F}
    (hx : IsLevel t x) : U (proj k t x) = 0 := by
  set b : ℕ → (Finset (Fin i) → F) := fun l => (D ^ l) ((U ^ (l + (t - k) + 1)) x) with hb
  have h0 : U ((D ^ 0) ((U ^ (0 + (t - k))) x)) = b 0 := by
    rw [hb]
    simp only [pow_zero, Module.End.one_apply, zero_add]
    rw [pow_succ', Module.End.mul_apply]
  have hstep : ∀ l, l < k → projCoef F (i - 2 * k) (l + 1) •
      U ((D ^ (l + 1)) ((U ^ (l + 1 + (t - k))) x))
        = projCoef F (i - 2 * k) (l + 1) • b (l + 1) - projCoef F (i - 2 * k) l • b l := by
    intro l hl
    have hlev : IsLevel (k - (l + 1)) ((U ^ (l + 1 + (t - k))) x) :=
      IsLevel.map_U_pow _ (by rwa [show k - (l + 1) + (l + 1 + (t - k)) = t from by omega])
    rw [U_D_pow hlev l, smul_add, smul_smul, hb]
    simp only
    rw [← Module.End.mul_apply U, ← pow_succ', show l + (t - k) + 1 = l + 1 + (t - k) from by omega]
    have hc : projCoef F (i - 2 * k) (l + 1) *
        (((l : F) + 1) * ((i : F) - 2 * ((k - (l + 1) : ℕ) : F) - (l : F)))
          = -projCoef F (i - 2 * k) l := by
      rw [← projCoef_succ (F := F) (i - 2 * k) l, Nat.cast_sub (show l + 1 ≤ k from by omega),
        Nat.cast_sub hk]
      push_cast
      ring
    rw [hc, neg_smul, sub_eq_add_neg]
  rw [proj_apply, map_smul, map_sum, Finset.sum_range_succ']
  simp only [map_smul]
  rw [Finset.sum_congr rfl (fun l hl => hstep l (Finset.mem_range.mp hl)), h0,
    Finset.sum_range_sub (fun l => projCoef F (i - 2 * k) l • b l), sub_add_cancel]
  have hbk : b k = 0 := by
    rw [hb]
    simp only
    rw [hx.U_pow_eq_zero (by omega), map_zero]
  rw [hbk, smul_zero, smul_zero]

omit [CharZero F] in
theorem factorial_mul_strCoef_zero {k r : ℕ} (hk : 2 * k ≤ i) (hr : r ≤ i - 2 * k) :
    ((i - 2 * k - r)! : F) * strCoef F i k 0 r = (r ! : F) * ((i - 2 * k)! : F) := by
  have e1 : strCoef F i k 0 r
      = ((r.descFactorial r : ℕ) : F) * (((i - 2 * k - r + 1).ascFactorial r : ℕ) : F) := by
    rw [strCoef, Finset.prod_mul_distrib, Nat.descFactorial_eq_prod_range,
      Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_prod]
    congr 1
    · exact Finset.prod_congr rfl fun u _ => by rw [zero_add]
    · refine Finset.prod_congr rfl fun u _ => ?_
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hr, Nat.cast_sub hk]
      push_cast
      ring
  have e2 := Nat.factorial_mul_ascFactorial (i - 2 * k - r) r
  rw [show i - 2 * k - r + r = i - 2 * k from by omega] at e2
  rw [e1, Nat.descFactorial_self, ← e2]
  push_cast
  ring

theorem proj_string {k t k' : ℕ} (hkt : k ≤ t) (hkit : k ≤ i - t) (hti : t ≤ i) (hk't : k' ≤ t)
    {h : Finset (Fin i) → F} (hh : IsPrim k' h) :
    proj k t ((D ^ (t - k')) h) = if k' = k then h else 0 := by
  rcases Nat.lt_trichotomy k' k with hlt | heq | hgt
  · rw [ite_eq_right (by omega)]
    obtain ⟨e, rfl⟩ : ∃ e, k = k' + e + 1 := ⟨k - k' - 1, by omega⟩
    have hex : ∃ c : F, proj (k' + e + 1) t ((D ^ (t - k')) h) = c • (D ^ (e + 1)) h := by
      rw [proj_apply]
      have hterm : ∀ l, ∃ c : F,
          (D ^ l) ((U ^ (l + (t - (k' + e + 1)))) ((D ^ (t - k')) h)) = c • (D ^ (e + 1)) h := by
        intro l
        rcases Nat.lt_or_ge (e + 1) l with hl | hl
        · exact ⟨0, by rw [hh.U_pow_D_pow_eq_zero (by omega), map_zero, zero_smul]⟩
        · refine ⟨strCoef F i k' (e + 1 - l) (l + (t - (k' + e + 1))), ?_⟩
          have := hh.U_pow_D_pow (e + 1 - l) (l + (t - (k' + e + 1)))
          rw [show e + 1 - l + (l + (t - (k' + e + 1))) = t - k' from by omega] at this
          rw [this, map_smul, ← Module.End.mul_apply, ← pow_add,
            show l + (e + 1 - l) = e + 1 from by omega]
      choose c hc using hterm
      refine ⟨(((i - 2 * (k' + e + 1) - (t - (k' + e + 1)))! : F)
        / (((t - (k' + e + 1))! : F) * ((i - 2 * (k' + e + 1))! : F)))
          * ∑ l ∈ range (k' + e + 1 + 1), projCoef F (i - 2 * (k' + e + 1)) l * c l, ?_⟩
      rw [← smul_smul, Finset.sum_smul]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by rw [hc l, smul_smul]
    obtain ⟨c, hc⟩ := hex
    have hU := U_proj (F := F) hkt (show 2 * (k' + e + 1) ≤ i from by omega)
      (by simpa [show k' + (t - k') = t from by omega] using hh.1.map_D_pow (t - k'))
    rw [hc, map_smul, hh.U_string e] at hU
    have hne : ((e : F) + 1) * ((i : F) - 2 * (k' : F) - (e : F)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero e) ?_
      have h1 : (i : F) - 2 * (k' : F) - (e : F) = ((i - 2 * k' - e : ℕ) : F) := by
        rw [Nat.cast_sub (show e ≤ i - 2 * k' from by omega),
          Nat.cast_sub (show 2 * k' ≤ i from by omega)]
        push_cast
        ring
      rw [h1]
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [smul_smul, mul_comm, ← smul_smul] at hU
    have h2 : c • (D ^ e) h = 0 := by
      rcases smul_eq_zero.mp hU with h3 | h3
      · exact absurd h3 hne
      · exact h3
    rw [hc, pow_succ', Module.End.mul_apply, ← map_smul, h2, map_zero]
  · subst heq
    rw [ite_eq_left rfl, proj_apply, Finset.sum_range_succ',
      Finset.sum_eq_zero (fun l _ => by
        rw [hh.U_pow_D_pow_eq_zero (by omega), map_zero, smul_zero])]
    have h0 := hh.U_pow_D_pow 0 (t - k')
    rw [zero_add] at h0
    rw [zero_add, zero_add, h0, pow_zero, Module.End.one_apply, Module.End.one_apply, smul_smul,
      smul_smul]
    have hf := factorial_mul_strCoef_zero (F := F) (i := i) (k := k') (r := t - k')
      (by omega) (by omega)
    have h1 : (((t - k')! : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (((i - 2 * k')! : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : (((i - 2 * k' + 1)! : ℕ) : F) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hone : ((i - 2 * k' - (t - k'))! : F) / (((t - k')! : F) * ((i - 2 * k')! : F))
        * (projCoef F (i - 2 * k') 0 * strCoef F i k' 0 (t - k')) = 1 := by
      rw [projCoef]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, add_zero]
      rw [div_self h3, one_mul, div_mul_eq_mul_div, hf]
      exact div_self (mul_ne_zero h1 h2)
    rw [mul_assoc, hone, one_smul]
  · rw [ite_eq_right (by omega), proj_apply,
      Finset.sum_eq_zero (fun l _ => by
        rw [hh.U_pow_D_pow_eq_zero (by omega), map_zero, smul_zero]), smul_zero]

theorem proj_decomp {k t : ℕ} (hkt : k ≤ t) (hkit : k ≤ i - t) (hti : t ≤ i)
    {y : ℕ → (Finset (Fin i) → F)} (hy : ∀ k', IsPrim k' (y k')) :
    proj k t (∑ k' ∈ range (t + 1), (D ^ (t - k')) (y k')) = y k := by
  rw [map_sum, Finset.sum_congr rfl (fun k' hk' =>
    proj_string hkt hkit hti (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')) (hy k')),
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega))]

theorem proj_isPrim {k t : ℕ} (hkt : k ≤ t) (hkit : k ≤ i - t) (hti : t ≤ i)
    {x : Finset (Fin i) → F} (hx : IsLevel t x) : IsPrim k (proj k t x) := by
  obtain ⟨y, hy, hxy⟩ := exists_prim_decomp t x hx
  rw [hxy, proj_decomp hkt hkit hti hy]
  exact hy k

theorem sum_D_proj {t : ℕ} (hti : t ≤ i) {x : Finset (Fin i) → F} (hx : IsLevel t x) :
    ∑ k ∈ range (min t (i - t) + 1), (D ^ (t - k)) (proj k t x) = x := by
  obtain ⟨y, hy, hxy⟩ := exists_prim_decomp t x hx
  have hp : ∀ k ∈ range (min t (i - t) + 1), (D ^ (t - k)) (proj k t x) = (D ^ (t - k)) (y k) := by
    intro k hk
    have hk' : k ≤ min t (i - t) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hxy, proj_decomp (le_trans hk' (min_le_left _ _)) (le_trans hk' (min_le_right _ _))
      hti hy]
  rw [Finset.sum_congr rfl hp]
  have hsub : range (min t (i - t) + 1) ⊆ range (t + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  rw [Finset.sum_subset hsub, ← hxy]
  intro k hk hk2
  rw [Finset.mem_range] at hk hk2
  exact (hy k).D_pow_eq_zero (by omega)

end CharZero

end Rhone.LinearAlgebra.BooleanLatticeInverse
