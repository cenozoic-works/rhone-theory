/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GenericField.Tower
public import Rhone.Algebra.E22

/-! # `E_{2,2}` is irreducible over every field in which `2 ≠ 0` -/

@[expose] public section

namespace Rhone.Algebra.GenericField

open Polynomial

variable (K : Type*) [Field K]

noncomputable def E22a : Fuv K := uu K + 2
noncomputable def E22b : Fuv K := (uu K + 2) * (3 * uu K + 13)
noncomputable def E22c : Fuv K := 2 * (uu K + 1) * (uu K + 3) * (uu K + 6)

noncomputable def E22 : P K := C (E22a K) * X ^ 2 + C (E22b K) * X + C (E22c K)

theorem E22a_rat : E22a ℚ = _root_.Rhone.Algebra.E22a := rfl
theorem E22b_rat : E22b ℚ = _root_.Rhone.Algebra.E22b := rfl
theorem E22c_rat : E22c ℚ = _root_.Rhone.Algebra.E22c := rfl

theorem E22_rat : E22 ℚ = _root_.Rhone.Algebra.E22 := rfl

theorem E22a_ne_zero : E22a K ≠ 0 := uu_add_two_ne_zero K

theorem E22_natDegree : (E22 K).natDegree = 2 :=
  Polynomial.natDegree_quadratic (E22a_ne_zero K)

theorem E22_ne_zero : E22 K ≠ 0 := by
  intro h
  have h2 := E22_natDegree K
  rw [h, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

noncomputable def Qc : Polynomial (Fv K) := X ^ 3 + 16 * X ^ 2 + 109 * X + 194

noncomputable def Dsc : Polynomial (Fv K) := (X + 2) * Qc K

theorem map_Dsc :
    algebraMap (Polynomial (Fv K)) (Fuv K) (Dsc K) = discrim (E22a K) (E22b K) (E22c K) := by
  simp only [Dsc, Qc, E22a, E22b, E22c, uu, discrim, map_add, map_mul, map_pow, map_ofNat,
    RatFunc.algebraMap_X]
  ring

theorem c32_ne_zero (h2 : (2 : K) ≠ 0) : (32 : Fv K) ≠ 0 := by
  have hK : (32 : K) ≠ 0 := by
    have h : (32 : K) = 2 ^ 5 := by norm_num
    rw [h]; exact pow_ne_zero _ h2
  intro hz
  apply hK
  apply (RatFunc.C (K := K)).injective
  rw [map_ofNat, map_zero]
  exact hz

theorem Qc_eval_neg_two : (Qc K).eval (-2 : Fv K) = 32 := by
  simp only [Qc, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  ring

theorem X_sub_C_neg_two : (X - C (-2 : Fv K)) = (X + 2 : Polynomial (Fv K)) := by
  rw [map_neg, sub_neg_eq_add, map_ofNat]

theorem discrim_ne_sq (h2 : (2 : K) ≠ 0) (s : Fuv K) :
    discrim (E22a K) (E22b K) (E22c K) ≠ s ^ 2 := by
  intro hs
  rw [← map_Dsc] at hs
  have hroot : s ^ 2 + algebraMap (Polynomial (Fv K)) (Fuv K) 0 * s
      + algebraMap (Polynomial (Fv K)) (Fuv K) (-(Dsc K)) = 0 := by
    rw [map_zero, map_neg, ← hs]; ring
  obtain ⟨y, hy⟩ := _root_.Rhone.Algebra.descend (0 : Polynomial (Fv K)) (-(Dsc K)) s hroot
  have hy2 : y ^ 2 = Dsc K := by linear_combination hy
  have hprime : Prime (X - C (-2 : Fv K)) := (Polynomial.irreducible_X_sub_C _).prime
  have hDsc : Dsc K = (X - C (-2 : Fv K)) * Qc K := by rw [X_sub_C_neg_two]; rfl
  have hdvd_y : (X - C (-2 : Fv K)) ∣ y :=
    hprime.dvd_of_dvd_pow (n := 2) (by rw [hy2, hDsc]; exact Dvd.intro _ rfl)
  obtain ⟨z, hz⟩ := hdvd_y
  have hne : (X - C (-2 : Fv K)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hQ : (X - C (-2 : Fv K)) * ((X - C (-2 : Fv K)) * z ^ 2)
      = (X - C (-2 : Fv K)) * Qc K := by
    rw [← hDsc, ← hy2, hz]; ring
  have hQdvd : (X - C (-2 : Fv K)) ∣ Qc K := ⟨z ^ 2, (mul_left_cancel₀ hne hQ).symm⟩
  have hroot2 : (Qc K).IsRoot (-2 : Fv K) := Polynomial.dvd_iff_isRoot.mp hQdvd
  rw [Polynomial.IsRoot, Qc_eval_neg_two] at hroot2
  exact c32_ne_zero K h2 hroot2

theorem E22_no_root (h2 : (2 : K) ≠ 0) (r : Fuv K) : ¬ (E22 K).IsRoot r := by
  intro hr
  have hquad : E22a K * (r * r) + E22b K * r + E22c K = 0 := by
    have h := hr
    simp only [Polynomial.IsRoot, E22, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at h
    linear_combination h
  exact quadratic_ne_zero_of_discrim_ne_sq (discrim_ne_sq K h2) r hquad

theorem E22_irreducible (h2 : (2 : K) ≠ 0) : Irreducible (E22 K) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [E22_natDegree]; decide
  · exact E22_no_root K h2

theorem E22_prime (h2 : (2 : K) ≠ 0) : Prime (E22 K) := (E22_irreducible K h2).prime

theorem E22_irreducible_of_charZero [CharZero K] : Irreducible (E22 K) :=
  E22_irreducible K (by norm_num)

theorem E22_irreducible_rat : Irreducible _root_.Rhone.Algebra.E22 :=
  E22_rat ▸ E22_irreducible_of_charZero ℚ

theorem two_ne_zero_ratFunc (h2 : (2 : K) ≠ 0) : (2 : RatFunc K) ≠ 0 := by
  intro hz
  exact h2 ((RatFunc.C (K := K)).injective (by rw [map_ofNat, map_zero]; exact hz))

theorem E22_irreducible_pi : Irreducible (E22 (RatFunc (RatFunc ℚ))) :=
  E22_irreducible _ (two_ne_zero_ratFunc _ (two_ne_zero_ratFunc ℚ (by norm_num)))

theorem E22_reducible_char_two (h2 : (2 : K) = 0) : ¬ Irreducible (E22 K) := by
  have h2' : (2 : Fuv K) = 0 := by
    rw [show (2 : Fuv K) = algebraMap K (Fuv K) 2 from (map_ofNat _ 2).symm, h2, map_zero]
  have hc : E22c K = 0 := by rw [E22c, h2']; ring
  have hfac : E22 K = X * (C (E22a K) * X + C (E22b K)) := by
    rw [E22, hc]; simp; ring
  intro hirr
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit h) (by simp)
  · have hdeg : (C (E22a K) * X + C (E22b K)).natDegree = 1 :=
      Polynomial.natDegree_linear (E22a_ne_zero K)
    exact absurd (Polynomial.natDegree_eq_zero_of_isUnit h) (by rw [hdeg]; norm_num)

theorem E22_irreducible_iff : Irreducible (E22 K) ↔ (2 : K) ≠ 0 :=
  ⟨fun h h2 => E22_reducible_char_two K h2 h, E22_irreducible K⟩

end Rhone.Algebra.GenericField
