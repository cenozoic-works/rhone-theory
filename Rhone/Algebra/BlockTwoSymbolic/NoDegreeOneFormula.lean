/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Tower
public import Rhone.Algebra.SymbolicFrequencies.NoFormula

/-! # No degree-one formula for the coalescent `q22` with symbolic mutant frequencies -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

theorem no_degree_one_formula_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      _root_.Rhone.Algebra.DAdm (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) 1
          e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 := by
  rw [eq_q22π_of_isSolutionπ hq]
  exact SymbolicFrequencies.no_degree_one_formula_pi

theorem two_le_degree_of_formula_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) {D : ℕ}
    {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
    (he : _root_.Rhone.Algebra.DAdm (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) D e)
    (hval : Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e = q
        s22) :
    2 ≤ D :=
  SymbolicFrequencies.two_le_degree_of_formula_pi he (hval.trans (eq_q22π_of_isSolutionπ hq))

theorem no_degree_one_formula_total_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), GenericField.TotalDAdm
        SymbolicFrequencies.Kpi 1 e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 := by
  rw [eq_q22π_of_isSolutionπ hq]
  exact SymbolicFrequencies.no_degree_one_formula_total_pi

theorem two_le_degree_of_formula_total_pi_coalescent
    {q : St → GenericField.L SymbolicFrequencies.Kpi} (hq : IsSolutionπ q)
    {D : ℕ} {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
        (he : GenericField.TotalDAdm SymbolicFrequencies.Kpi D e)
    (hval : Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e = q
        s22) :
    2 ≤ D :=
  SymbolicFrequencies.two_le_degree_of_formula_total_pi he (hval.trans (eq_q22π_of_isSolutionπ hq))

section ClosedForm

local notation "uPi" => (Polynomial.C (GenericField.uu SymbolicFrequencies.Kpi) : GenericField.P SymbolicFrequencies.Kpi)
local notation "vPi" => (Polynomial.C (GenericField.vv SymbolicFrequencies.Kpi) : GenericField.P SymbolicFrequencies.Kpi)
local notation "aPi"
    => (Polynomial.C SymbolicFrequencies.piAF : GenericField.P SymbolicFrequencies.Kpi)
local notation "bPi"
    => (Polynomial.C SymbolicFrequencies.piBF : GenericField.P SymbolicFrequencies.Kpi)

noncomputable def E22L : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      (GenericField.E22 SymbolicFrequencies.Kpi)

theorem algebraMap_uuL : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi) (GenericField.uu SymbolicFrequencies.Kpi)
    = GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB SymbolicFrequencies.Kpi := by
  rw [uu_eq, map_add, algebraMap_thAF, algebraMap_thBF]

theorem algebraMap_vvL : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
    = GenericField.thA SymbolicFrequencies.Kpi - GenericField.thB SymbolicFrequencies.Kpi := by
  rw [vv_eq, map_sub, algebraMap_thAF, algebraMap_thBF]

theorem E22P_eq : GenericField.E22 SymbolicFrequencies.Kpi
    = (uPi + 2) * X ^ 2 + (uPi + 2) * (3 * uPi + 13) * X
      + 2 * (uPi + 1) * (uPi + 3) * (uPi + 6) := by
  rw [GenericField.E22, GenericField.E22a, GenericField.E22b, GenericField.E22c]
  simp only [map_add, map_mul, map_ofNat, map_one]

theorem W46_closed_form {R : Type*} [CommRing R] (u v a b r : R) :
    W46 u v a b r = (1 - a) * (1 - b)
      * (((1 - a) * (u + v) + 2) * ((1 - b) * (u - v) + 2)
          * ((u + 2) * r ^ 2 + (u + 2) * (3 * u + 13) * r + 2 * (u + 1) * (u + 3) * (u + 6))
        + a * b * (u + v) * (u - v) * ((u + 2) * r + 2 * (u + 3) * (u + 6))) := by
  simp only [W46]
  ring

theorem Nqπ_closed_form :
    SymbolicFrequencies.Nqπ = (1 - aPi) * (1 - bPi)
      * (((1 - aPi) * (uPi + vPi) + 2) * ((1 - bPi) * (uPi - vPi) + 2) * GenericField.E22
          SymbolicFrequencies.Kpi
        + aPi * bPi * (uPi + vPi) * (uPi - vPi)
          * ((uPi + 2) * X + 2 * (uPi + 3) * (uPi + 6))) := by
  rw [← Wπ_s22, Wπ, s22, Wval_46, W46_closed_form, E22P_eq]

theorem q22π_mul_denom :
    SymbolicFrequencies.q22π * algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) SymbolicFrequencies.Dqπ
      = algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
          SymbolicFrequencies.Nqπ := by
  have h : SymbolicFrequencies.q22π = algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) SymbolicFrequencies.Nqπ
      / algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
          SymbolicFrequencies.Dqπ := rfl
  rw [h]
  exact div_mul_cancel₀ _ (polyL_ne_zero SymbolicFrequencies.Dqπ_ne_zero)

theorem algebraMap_Dqπ :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        SymbolicFrequencies.Dqπ
      = 4 * ((GenericField.thA SymbolicFrequencies.Kpi + 1) *
          (GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L) := by
  rw [SymbolicFrequencies.Dqπ_eq, map_mul, algebraMap_P_C, SymbolicFrequencies.gfacπ, E22L]
  simp only [map_mul, map_add, map_sub, map_ofNat, algebraMap_uuL, algebraMap_vvL]
  ring

theorem denom_ne_zero :
    (GenericField.thA SymbolicFrequencies.Kpi + 1) *
        (GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L ≠ 0 := by
  intro hz
  refine polyL_ne_zero SymbolicFrequencies.Dqπ_ne_zero ?_
  rw [algebraMap_Dqπ, hz, mul_zero]

theorem algebraMap_Nqπ :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        SymbolicFrequencies.Nqπ
      = 4 * ((1 - piAL) * (1 - piBL)
        * (((1 - piAL) * GenericField.thA SymbolicFrequencies.Kpi + 1) *
            ((1 - piBL) * GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L
          + piAL * piBL * GenericField.thA SymbolicFrequencies.Kpi * GenericField.thB
              SymbolicFrequencies.Kpi
            * ((GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                SymbolicFrequencies.Kpi + 2) * GenericField.rhoL SymbolicFrequencies.Kpi
              + 2 * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                  SymbolicFrequencies.Kpi + 3)
                * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                    SymbolicFrequencies.Kpi + 6)))) := by
  rw [Nqπ_closed_form, E22L]
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat, algebraMap_uPi, algebraMap_vPi,
    algebraMap_aPi, algebraMap_bPi, algebraMap_X_L]
  ring

theorem q22π_closed_form :
    SymbolicFrequencies.q22π = ((1 - piAL) * (1 - piBL)
        * (((1 - piAL) * GenericField.thA SymbolicFrequencies.Kpi + 1) *
            ((1 - piBL) * GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L
          + piAL * piBL * GenericField.thA SymbolicFrequencies.Kpi * GenericField.thB
              SymbolicFrequencies.Kpi
            * ((GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                SymbolicFrequencies.Kpi + 2) * GenericField.rhoL SymbolicFrequencies.Kpi
              + 2 * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                  SymbolicFrequencies.Kpi + 3)
                * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                    SymbolicFrequencies.Kpi + 6))))
      / ((GenericField.thA SymbolicFrequencies.Kpi + 1) *
          (GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L) := by
  have h := q22π_mul_denom
  rw [algebraMap_Dqπ, algebraMap_Nqπ] at h
  rw [eq_div_iff denom_ne_zero]
  linear_combination h / 4

theorem closed_form_of_isSolutionπ {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    q s22 = ((1 - piAL) * (1 - piBL)
        * (((1 - piAL) * GenericField.thA SymbolicFrequencies.Kpi + 1) *
            ((1 - piBL) * GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L
          + piAL * piBL * GenericField.thA SymbolicFrequencies.Kpi * GenericField.thB
              SymbolicFrequencies.Kpi
            * ((GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                SymbolicFrequencies.Kpi + 2) * GenericField.rhoL SymbolicFrequencies.Kpi
              + 2 * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                  SymbolicFrequencies.Kpi + 3)
                * (GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB
                    SymbolicFrequencies.Kpi + 6))))
      / ((GenericField.thA SymbolicFrequencies.Kpi + 1) *
          (GenericField.thB SymbolicFrequencies.Kpi + 1) * E22L) :=
  (eq_q22π_of_isSolutionπ hq).trans q22π_closed_form

end ClosedForm

end Rhone.Algebra.BlockTwoSymbolic
