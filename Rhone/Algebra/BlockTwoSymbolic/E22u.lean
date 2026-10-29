/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.E22u
public import Rhone.Algebra.SymbolicFrequencies.Tower

/-! # `Ẽ₂` as a cubic in `u`, irreducible over `ℚ(π_A, π_B)(v, ρ)` -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

theorem cubic_no_root_rat (y : ℚ) : y ^ 3 + 23 * y ^ 2 + 148 * y + 256 ≠ 0 := by
  intro hy
  have h1 : y ^ 3 + algebraMap ℤ ℚ 23 * y ^ 2 + algebraMap ℤ ℚ 148 * y
      + algebraMap ℤ ℚ 256 = 0 := by
    simpa only [map_ofNat] using hy
  obtain ⟨m, hm⟩ := _root_.Rhone.Algebra.descend3 (23 : ℤ) 148 256 y h1
  exact _root_.Rhone.Algebra.no_int_root_cubic m hm

theorem cubic_no_root_C {K : Type*} [Field K]
    (h : ∀ y : K, y ^ 3 + 23 * y ^ 2 + 148 * y + 256 ≠ 0) (x : RatFunc K) :
    x ^ 3 + 23 * x ^ 2 + 148 * x + 256 ≠ 0 := by
  intro hx
  have h1 : x ^ 3 + algebraMap (Polynomial K) (RatFunc K) 23 * x ^ 2
      + algebraMap (Polynomial K) (RatFunc K) 148 * x
      + algebraMap (Polynomial K) (RatFunc K) 256 = 0 := by
    simpa only [map_ofNat] using hx
  obtain ⟨Y, hY⟩ := _root_.Rhone.Algebra.descend3 (23 : Polynomial K) 148 256 x h1
  have h2 := congrArg (Polynomial.eval (0 : K)) hY
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_zero] at h2
  exact h (Y.eval 0) h2

theorem cubic_no_root_Kpi (y : SymbolicFrequencies.Kpi) : y ^ 3 + 23 * y ^ 2 + 148 * y + 256 ≠ 0 :=
  cubic_no_root_C (cubic_no_root_C cubic_no_root_rat) y

theorem cubic_no_root_Fv (y : GenericField.Fv SymbolicFrequencies.Kpi) : y ^ 3 + 23 * y ^ 2 + 148 *
    y + 256 ≠ 0 :=
  cubic_no_root_C cubic_no_root_Kpi y

noncomputable abbrev rhoMπ : GenericField.Fuv SymbolicFrequencies.Kpi := GenericField.uu
    SymbolicFrequencies.Kpi

noncomputable def E22uπ : GenericField.P SymbolicFrequencies.Kpi :=
  C 2 * X ^ 3 + C (3 * rhoMπ + 20) * X ^ 2 + C (rhoMπ ^ 2 + 19 * rhoMπ + 54) * X
    + C (2 * rhoMπ ^ 2 + 26 * rhoMπ + 36)

theorem E22uπ_natDegree : E22uπ.natDegree = 3 :=
  Polynomial.natDegree_cubic (by norm_num)

theorem E22uπ_ne_zero : E22uπ ≠ 0 := by
  intro h
  have h2 := E22uπ_natDegree
  rw [h, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

noncomputable def B₂π : Polynomial (GenericField.Fv SymbolicFrequencies.Kpi) := 3 * X + 20
noncomputable def C₂π : Polynomial (GenericField.Fv SymbolicFrequencies.Kpi) := 2 *
    (X ^ 2 + 19 * X + 54)
noncomputable def D₂π : Polynomial (GenericField.Fv SymbolicFrequencies.Kpi) := 4 *
    (2 * X ^ 2 + 26 * X + 36)

theorem map_B₂π : algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
    (GenericField.Fuv SymbolicFrequencies.Kpi) B₂π
    = 3 * rhoMπ + 20 := by
  simp [B₂π, GenericField.uu, map_ofNat, RatFunc.algebraMap_X]

theorem map_C₂π : algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
    (GenericField.Fuv SymbolicFrequencies.Kpi) C₂π
    = 2 * (rhoMπ ^ 2 + 19 * rhoMπ + 54) := by
  simp [C₂π, GenericField.uu, map_ofNat, RatFunc.algebraMap_X]

theorem map_D₂π : algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
    (GenericField.Fuv SymbolicFrequencies.Kpi) D₂π
    = 4 * (2 * rhoMπ ^ 2 + 26 * rhoMπ + 36) := by
  simp [D₂π, GenericField.uu, map_ofNat, RatFunc.algebraMap_X]

theorem E22uπ_no_root (r : GenericField.Fuv SymbolicFrequencies.Kpi) : ¬ E22uπ.IsRoot r := by
  intro hr
  have hcub : 2 * r ^ 3 + (3 * rhoMπ + 20) * r ^ 2 + (rhoMπ ^ 2 + 19 * rhoMπ + 54) * r
      + (2 * rhoMπ ^ 2 + 26 * rhoMπ + 36) = 0 := by
    have h := hr
    simp only [Polynomial.IsRoot, E22uπ, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at h
    linear_combination h
  have h1 : (2 * r) ^ 3
      + algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
          (GenericField.Fuv SymbolicFrequencies.Kpi) B₂π * (2 * r) ^ 2
      + algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
          (GenericField.Fuv SymbolicFrequencies.Kpi) C₂π * (2 * r)
      + algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
          (GenericField.Fuv SymbolicFrequencies.Kpi) D₂π = 0 := by
    rw [map_B₂π, map_C₂π, map_D₂π]
    linear_combination 4 * hcub
  obtain ⟨Y, hY⟩ := _root_.Rhone.Algebra.descend3 B₂π C₂π D₂π (2 * r) h1
  have hB : B₂π.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi) = 23 := by norm_num [B₂π]
  have hC : C₂π.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi) = 148 := by norm_num [C₂π]
  have hD : D₂π.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi) = 256 := by norm_num [D₂π]
  have h3 : (Y.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi)) ^ 3 + 23 *
      (Y.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi)) ^ 2
      + 148 * (Y.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi)) + 256 = 0 := by
    have h := congrArg (Polynomial.eval (1 : GenericField.Fv SymbolicFrequencies.Kpi)) hY
    simpa [hB, hC, hD] using h
  exact cubic_no_root_Fv _ h3

theorem E22uπ_irreducible : Irreducible E22uπ := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [E22uπ_natDegree]; decide
  · exact E22uπ_no_root

theorem E22uπ_prime : Prime E22uπ := E22uπ_irreducible.prime

theorem middle_monic_quadratic_ne_zero (b c : GenericField.Fv SymbolicFrequencies.Kpi) :
    rhoMπ ^ 2 + algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
        (GenericField.Fuv SymbolicFrequencies.Kpi) b * rhoMπ
      + algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
          (GenericField.Fuv SymbolicFrequencies.Kpi) c ≠ 0 := by
  have hm : (X ^ 2 + (C b * X + C c) : Polynomial
      (GenericField.Fv SymbolicFrequencies.Kpi)).Monic :=
    Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
  have h : algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
      (GenericField.Fuv SymbolicFrequencies.Kpi) (X ^ 2 + (C b * X + C c))
      = rhoMπ ^ 2 + algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
          (GenericField.Fuv SymbolicFrequencies.Kpi) b * rhoMπ
        + algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
            (GenericField.Fuv SymbolicFrequencies.Kpi) c := by
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      rhoMπ, GenericField.uu]
    exact (add_assoc _ _ _).symm
  rw [← h]
  exact _root_.Rhone.Algebra.algebraMap_ne_zero hm.ne_zero

end Rhone.Algebra.BlockTwoSymbolic
