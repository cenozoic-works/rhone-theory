/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.NoFormula
public import Rhone.Algebra.GenericField.Swap
public import Rhone.Algebra.GenericField.TotalDegree

/-! # No degree-two formula for `q22`, transferred through the variable swap -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open KilledSystem

theorem eq_q22u_of_swapL_eq {q : St → L} (hq : IsSolution q) {x : L}
    (hx : GenericField.swapL x = q s22) : x = q22u := by
  apply GenericField.swapL_injective
  rw [hx, eq_q22_of_isSolution hq]
  exact GenericField.swapL_q22u.symm

theorem no_degree_two_formula_coalescent_swap {q : St → L} (hq : IsSolution q) :
    ¬ ∃ e : Expr Fuv, DAdm thAu thBu rhoU 2 e
        ∧ GenericField.swapL (Expr.eval thAu thBu rhoU e) = q s22 := by
  rintro ⟨e, he, hval⟩
  exact no_degree_two_formula ⟨e, he, eq_q22u_of_swapL_eq hq hval⟩

theorem three_le_degree_of_formula_coalescent_swap {q : St → L} (hq : IsSolution q) {D : ℕ}
    {e : Expr Fuv} (he : DAdm thAu thBu rhoU D e)
    (hval : GenericField.swapL (Expr.eval thAu thBu rhoU e) = q s22) : 3 ≤ D :=
  three_le_degree_of_formula he (eq_q22u_of_swapL_eq hq hval)

theorem no_degree_two_formula_total_coalescent_swap {q : St → L} (hq : IsSolution q) :
    ¬ ∃ e : Expr Fuv, GenericField.TotalDAdmU 2 e
        ∧ GenericField.swapL (Expr.eval thAu thBu rhoU e) = q s22 := by
  rintro ⟨e, he, hval⟩
  exact GenericField.no_degree_two_formula_total ⟨e, he, eq_q22u_of_swapL_eq hq hval⟩

theorem three_le_degree_of_formula_total_coalescent_swap {q : St → L} (hq : IsSolution q) {D : ℕ}
    {e : Expr Fuv} (he : GenericField.TotalDAdmU D e)
    (hval : GenericField.swapL (Expr.eval thAu thBu rhoU e) = q s22) : 3 ≤ D :=
  GenericField.three_le_degree_of_formula_total he (eq_q22u_of_swapL_eq hq hval)

end Rhone.Algebra.KilledSystemULast
