/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Q22Data

/-! # `E_{2,2}` is a factor of `den(q22)` -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

noncomputable def q22 : L :=
  algebraMap P L Nq / algebraMap P L Dq

theorem Dq_eq : Dq = C Gq * E22 := by
  simp only [Dq, Gq, E22, E22a, E22b, E22c, qD2, qD1, qD0,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem Gq_ne_zero : Gq ≠ 0 := by
  have h : Gq = 75 * ((uu - vv + 2) * (uu + vv + 2)) := by simp only [Gq]; ring
  rw [h]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero uu_sub_vv_add_two_ne_zero uu_add_vv_add_two_ne_zero)

theorem Dq_ne_zero : Dq ≠ 0 := by
  rw [Dq_eq]
  exact mul_ne_zero (fun h => Gq_ne_zero (Polynomial.C_eq_zero.mp h)) E22_ne_zero

theorem E22_dvd_Dq : E22 ∣ Dq := ⟨C Gq, by rw [Dq_eq]; ring⟩

theorem Nq_mod : C E22a * Nq = C Hq * E22 + Remq := by
  simp only [Nq, Remq, E22, E22a, E22b, E22c, Hq, qN2, qN1, qN0, Rem1, Rem0,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem Rem1_ne_zero : Rem1 ≠ 0 := by
  have h : Rem1 = 4 * ((uu + 2) * (uu + 2)) * ((uu - vv) * (uu + vv)) := by
    simp only [Rem1]; ring
  rw [h]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (mul_ne_zero uu_add_two_ne_zero uu_add_two_ne_zero))
    (mul_ne_zero uu_sub_vv_ne_zero uu_add_vv_ne_zero)

theorem Remq_ne_zero : Remq ≠ 0 := by
  intro h
  apply Rem1_ne_zero
  have h1 := congrArg (fun p => Polynomial.coeff p 1) h
  simpa [Remq] using h1

theorem Remq_natDegree_le : Remq.natDegree ≤ 1 := by
  rw [Remq]; exact Polynomial.natDegree_linear_le

theorem E22_not_dvd_Nq : ¬ E22 ∣ Nq := by
  intro hdvd
  have h1 : E22 ∣ Remq := by
    have hR : Remq = C E22a * Nq - C Hq * E22 := by rw [Nq_mod]; ring
    rw [hR]
    exact dvd_sub (hdvd.mul_left _) (Dvd.intro_left _ rfl)
  have h2 := Polynomial.natDegree_le_of_dvd h1 Remq_ne_zero
  rw [E22_natDegree] at h2
  exact absurd (le_trans h2 Remq_natDegree_le) (by norm_num)

theorem E22_dvd_q22_denom : E22 ∣ q22.denom :=
  prime_dvd_denom Dq_ne_zero rfl E22_prime E22_dvd_Dq E22_not_dvd_Nq

end Rhone.Algebra
