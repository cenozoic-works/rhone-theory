/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Q22uData

/-! # No Ewens-shaped formula of degree `2` for `q22` -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

noncomputable def thAu : L := algebraMap P L (C (2 : Fuv)⁻¹ * (X + C vv))
noncomputable def thBu : L := algebraMap P L (C (2 : Fuv)⁻¹ * (X - C vv))
noncomputable def rhoU : L := algebraMap Fuv L rhoM

theorem boundedDen_thAu (D : ℕ) : BoundedDen D thAu := boundedDen_of_poly D _
theorem boundedDen_thBu (D : ℕ) : BoundedDen D thBu := boundedDen_of_poly D _
theorem boundedDen_rhoU (D : ℕ) : BoundedDen D rhoU := boundedDen_coeff D _

noncomputable def q22u : L := algebraMap P L NqU / algebraMap P L DqU

theorem DqU_eq : DqU = GqU * E22u := by
  simp only [DqU, GqU, E22u, duU5, duU4, duU3, duU2, duU1, duU0, guU2, guU1, guU0, rhoM, uu,
    map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring

theorem GqU_natDegree : GqU.natDegree = 2 :=
  Polynomial.natDegree_quadratic (a := guU2) (by rw [guU2]; norm_num)

theorem GqU_ne_zero : GqU ≠ 0 := by
  intro h
  have h2 := GqU_natDegree
  rw [h, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

theorem DqU_ne_zero : DqU ≠ 0 := by
  rw [DqU_eq]; exact mul_ne_zero GqU_ne_zero E22u_ne_zero

theorem E22u_dvd_DqU : E22u ∣ DqU := ⟨GqU, by rw [DqU_eq]; ring⟩

theorem NqU_mod : 8 * NqU = HqU * E22u + RemqU := by
  simp only [NqU, HqU, RemqU, E22u, nuU5, nuU4, nuU3, nuU2, nuU1, nuU0,
    huU2, huU1, huU0, ruU2, ruU1, ruU0, rhoM, uu,
    map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring

theorem ruU2_ne_zero : ruU2 ≠ 0 := by
  have hb : algebraMap Fv Fuv (3 : Fv) = (3 : Fuv) := map_ofNat _ 3
  have hc : algebraMap Fv Fuv (1 - RatFunc.X ^ 2 : Fv) = 1 - vv ^ 2 := by
    rw [map_sub, map_one, map_pow]; rfl
  have h := middle_monic_quadratic_ne_zero (3 : Fv) (1 - RatFunc.X ^ 2 : Fv)
  rw [hb, hc] at h
  have hEq : ruU2 = 64 * (uu ^ 2 + 3 * uu + (1 - vv ^ 2)) := by
    simp only [ruU2, rhoM]; ring
  rw [hEq]
  exact mul_ne_zero (by norm_num) h

theorem RemqU_ne_zero : RemqU ≠ 0 := by
  intro h
  apply ruU2_ne_zero
  have h1 := congrArg (fun p => Polynomial.coeff p 2) h
  simpa [RemqU] using h1

theorem RemqU_natDegree_le : RemqU.natDegree ≤ 2 := by
  rw [RemqU]; exact Polynomial.natDegree_quadratic_le

theorem E22u_not_dvd_NqU : ¬ E22u ∣ NqU := by
  intro hdvd
  have h1 : E22u ∣ RemqU := by
    have hR : RemqU = 8 * NqU - HqU * E22u := by rw [NqU_mod]; ring
    rw [hR]
    exact dvd_sub (hdvd.mul_left _) (Dvd.intro_left _ rfl)
  have h2 := Polynomial.natDegree_le_of_dvd h1 RemqU_ne_zero
  rw [E22u_natDegree] at h2
  exact absurd (le_trans h2 RemqU_natDegree_le) (by norm_num)

theorem E22u_dvd_q22u_denom : E22u ∣ q22u.denom :=
  prime_dvd_denom DqU_ne_zero rfl E22u_prime E22u_dvd_DqU E22u_not_dvd_NqU

theorem not_boundedDen_q22u : ¬ BoundedDen 2 q22u :=
  not_boundedDen DqU_ne_zero rfl E22u_prime E22u_dvd_DqU E22u_not_dvd_NqU
    (by rw [E22u_natDegree]; norm_num)

theorem no_degree_two_formula :
    ¬ ∃ e : Expr Fuv, DAdm thAu thBu rhoU 2 e ∧ Expr.eval thAu thBu rhoU e = q22u := by
  rintro ⟨e, he, hval⟩
  exact not_boundedDen_q22u
    (hval ▸ boundedDen_eval (boundedDen_thAu 2) (boundedDen_thBu 2) (boundedDen_rhoU 2) he)

theorem three_le_degree_of_formula {D : ℕ} {e : Expr Fuv} (he : DAdm thAu thBu rhoU D e)
    (hval : Expr.eval thAu thBu rhoU e = q22u) : 3 ≤ D := by
  have h := natDegree_le_of_dvd_denom_eval (boundedDen_thAu D) (boundedDen_thBu D)
      (boundedDen_rhoU D) he
    E22u_irreducible (by rw [hval]; exact E22u_dvd_q22u_denom)
  rwa [E22u_natDegree] at h

end Rhone.Algebra
