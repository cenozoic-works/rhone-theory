/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SymbolicFrequencies.Q22
public import Rhone.Algebra.GenericField.TotalDegree

/-! # No degree-one formula for `q22` over `ℚ(π_A, π_B)` with symbolic `π` -/

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

theorem not_boundedDen_q22π : ¬ _root_.Rhone.Algebra.BoundedDen 1 q22π :=
  _root_.Rhone.Algebra.not_boundedDen Dqπ_ne_zero rfl (GenericField.E22_prime Kpi two_ne_zero_Kpi)
    E22_dvd_Dqπ E22_not_dvd_Nqπ (by rw [GenericField.E22_natDegree]; norm_num)

theorem no_degree_one_formula_pi :
    ¬ ∃ e : Expr (GenericField.Fuv Kpi),
      _root_.Rhone.Algebra.DAdm (GenericField.thA Kpi) (GenericField.thB Kpi)
          (GenericField.rhoL Kpi) 1 e ∧
        Expr.eval (GenericField.thA Kpi) (GenericField.thB Kpi) (GenericField.rhoL Kpi) e = q22π :=
            by
  rintro ⟨e, he, hval⟩
  exact not_boundedDen_q22π
    (hval ▸ _root_.Rhone.Algebra.boundedDen_eval (GenericField.boundedDen_thA Kpi 1)
        (GenericField.boundedDen_thB Kpi 1)
      (GenericField.boundedDen_rhoL Kpi 1) he)

theorem two_le_degree_of_formula_pi {D : ℕ} {e : Expr (GenericField.Fuv Kpi)}
    (he : _root_.Rhone.Algebra.DAdm (GenericField.thA Kpi) (GenericField.thB Kpi)
        (GenericField.rhoL Kpi) D e)
    (hval : Expr.eval (GenericField.thA Kpi) (GenericField.thB Kpi) (GenericField.rhoL Kpi) e =
        q22π) : 2 ≤ D := by
  have h := _root_.Rhone.Algebra.natDegree_le_of_dvd_denom_eval (GenericField.boundedDen_thA Kpi D)
      (GenericField.boundedDen_thB Kpi D)
    (GenericField.boundedDen_rhoL Kpi D) he (GenericField.E22_irreducible Kpi two_ne_zero_Kpi)
    (by rw [hval]; exact E22_dvd_q22π_denom)
  rwa [GenericField.E22_natDegree] at h

theorem no_degree_one_formula_total_pi :
    ¬ ∃ e : Expr (GenericField.Fuv Kpi), GenericField.TotalDAdm Kpi 1 e
        ∧ Expr.eval (GenericField.thA Kpi) (GenericField.thB Kpi) (GenericField.rhoL Kpi) e =
            q22π := by
  rintro ⟨e, he, hval⟩
  exact no_degree_one_formula_pi ⟨e, he.toDAdm, hval⟩

theorem two_le_degree_of_formula_total_pi {D : ℕ} {e : Expr (GenericField.Fuv Kpi)}
    (he : GenericField.TotalDAdm Kpi D e)
    (hval : Expr.eval (GenericField.thA Kpi) (GenericField.thB Kpi) (GenericField.rhoL Kpi) e =
        q22π) : 2 ≤ D :=
  two_le_degree_of_formula_pi he.toDAdm hval

end Rhone.Algebra.SymbolicFrequencies
