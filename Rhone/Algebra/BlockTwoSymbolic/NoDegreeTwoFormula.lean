/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.TowerU

/-! # No degree-two formula for the coalescent `q22` with symbolic mutant frequencies -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

theorem boundedDen_thAuπ (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D thAuπ :=
  _root_.Rhone.Algebra.boundedDen_of_poly D _

theorem boundedDen_thBuπ (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D thBuπ :=
  _root_.Rhone.Algebra.boundedDen_of_poly D _

theorem boundedDen_rhoUπ (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D rhoUπ :=
  _root_.Rhone.Algebra.boundedDen_coeff D _

theorem not_boundedDen_q22πU : ¬ _root_.Rhone.Algebra.BoundedDen 2 q22πU :=
  _root_.Rhone.Algebra.not_boundedDen DcmUπ_ne_zero rfl E22uπ_prime E22uπ_dvd_DcmUπ
    E22uπ_not_dvd_WUs22 (by rw [E22uπ_natDegree]; norm_num)

theorem no_degree_two_formula_pi :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      _root_.Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ 2 e ∧
        Expr.eval thAuπ thBuπ rhoUπ e = q22πU := by
  rintro ⟨e, he, hval⟩
  exact not_boundedDen_q22πU
    (hval ▸ _root_.Rhone.Algebra.boundedDen_eval (boundedDen_thAuπ 2) (boundedDen_thBuπ 2)
        (boundedDen_rhoUπ 2) he)

theorem three_le_degree_of_formula_pi {D : ℕ} {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
    (he : _root_.Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ D e)
    (hval : Expr.eval thAuπ thBuπ rhoUπ e = q22πU) : 3 ≤ D := by
  have h := _root_.Rhone.Algebra.natDegree_le_of_dvd_denom_eval (boundedDen_thAuπ D)
      (boundedDen_thBuπ D)
    (boundedDen_rhoUπ D) he E22uπ_irreducible (by rw [hval]; exact E22uπ_dvd_q22πU_denom)
  rwa [E22uπ_natDegree] at h

theorem no_degree_two_formula_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      _root_.Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ 2 e ∧
        Expr.eval thAuπ thBuπ rhoUπ e = q s22 := by
  rw [eq_q22πU_of_isSolutionUπ hq]
  exact no_degree_two_formula_pi

theorem three_le_degree_of_formula_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) {D : ℕ}
        {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
    (he : _root_.Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ D e)
    (hval : Expr.eval thAuπ thBuπ rhoUπ e = q s22) : 3 ≤ D :=
  three_le_degree_of_formula_pi he (hval.trans (eq_q22πU_of_isSolutionUπ hq))

end Rhone.Algebra.BlockTwoSymbolic
