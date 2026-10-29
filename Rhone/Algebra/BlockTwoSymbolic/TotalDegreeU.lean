/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.NoDegreeTwoFormula
public import Rhone.Algebra.GenericField.TotalDegree

/-! # Definition 2.2 verbatim, `u`-last, over the coefficient field `ℚ(π_A, π_B)` -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

noncomputable def coeffHomUπ : SymbolicFrequencies.Kpi →+* GenericField.P SymbolicFrequencies.Kpi :=
  (Polynomial.C).comp
      ((algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi)).comp
    (algebraMap SymbolicFrequencies.Kpi (GenericField.Fv SymbolicFrequencies.Kpi)))

noncomputable def genUπ : Fin 3 → GenericField.P SymbolicFrequencies.Kpi :=
  ![C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
      (X + C (GenericField.vv SymbolicFrequencies.Kpi)),
    C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X - C (GenericField.vv SymbolicFrequencies.Kpi)),
    C rhoMπ]

noncomputable def evPUπ : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi →+* GenericField.P
    SymbolicFrequencies.Kpi :=
  MvPolynomial.eval₂Hom coeffHomUπ genUπ

noncomputable def evLUπ : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi →+* GenericField.L
    SymbolicFrequencies.Kpi :=
  (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi)).comp evPUπ

theorem evLUπ_apply (m : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi) :
    evLUπ m = algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (evPUπ m) := rfl

theorem genUπ_natDegree_le (i : Fin 3) : (genUπ i).natDegree ≤ 1 := by
  fin_cases i
  · exact le_trans Polynomial.natDegree_mul_le (by simp)
  · exact le_trans Polynomial.natDegree_mul_le (by simp)
  · simp [genUπ]

theorem natDegree_evPUπ_le (m : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi) :
    (evPUπ m).natDegree ≤ m.totalDegree := by
  rw [evPUπ, MvPolynomial.coe_eval₂Hom]
  exact GenericField.natDegree_eval₂_le _ (fun a => by simp [coeffHomUπ]) _ genUπ_natDegree_le m

theorem evLUπ_X_zero : evLUπ (MvPolynomial.X 0) = thAuπ := by
  simp [evLUπ, evPUπ, genUπ, thAuπ]

theorem evLUπ_X_one : evLUπ (MvPolynomial.X 1) = thBuπ := by
  simp [evLUπ, evPUπ, genUπ, thBuπ]

theorem evLUπ_X_two : evLUπ (MvPolynomial.X 2) = rhoUπ := by
  simp [evLUπ, evPUπ, genUπ, rhoUπ, RatFunc.algebraMap_C]

inductive TotalDAdmUπ (D : ℕ) : Expr (GenericField.Fuv SymbolicFrequencies.Kpi) → Prop
  | const (q : ℚ) : TotalDAdmUπ D (.const q)
  | coeff (x : GenericField.Fuv SymbolicFrequencies.Kpi) : TotalDAdmUπ D (.coeff x)
  | thA : TotalDAdmUπ D .thA
  | thB : TotalDAdmUπ D .thB
  | rho : TotalDAdmUπ D .rho
  | add {x y : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} : TotalDAdmUπ D x → TotalDAdmUπ D
      y →
      TotalDAdmUπ D (.add x y)
  | mul {x y : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} : TotalDAdmUπ D x → TotalDAdmUπ D
      y →
      TotalDAdmUπ D (.mul x y)
  | div {x g : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} (hx : TotalDAdmUπ D x)
      (hg : TotalDAdmUπ D g)
      (m : MvPolynomial (Fin 3) SymbolicFrequencies.Kpi) (hm : m.totalDegree ≤ D)
          (hne : evLUπ m ≠ 0)
      (hval : Expr.eval thAuπ thBuπ rhoUπ g = evLUπ m) :
      TotalDAdmUπ D (.div x g)

theorem TotalDAdmUπ.toDAdm {D : ℕ} {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
    (h : TotalDAdmUπ D e) :
    _root_.Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ D e := by
  induction h with
  | const q => exact .const q
  | coeff x => exact .coeff x
  | thA => exact .thA
  | thB => exact .thB
  | rho => exact .rho
  | add _ _ ihx ihy => exact .add ihx ihy
  | mul _ _ ihx ihy => exact .mul ihx ihy
  | div _ _ m hm hne hval ihx ihg =>
      refine .div ihx ihg (evPUπ m) ?_ (le_trans (natDegree_evPUπ_le m) hm) hval
      intro h0
      exact hne (by rw [evLUπ_apply, h0, map_zero])

theorem no_degree_two_formula_total_pi :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), TotalDAdmUπ 2 e
        ∧ Expr.eval thAuπ thBuπ rhoUπ e = q22πU := by
  rintro ⟨e, he, hval⟩
  exact no_degree_two_formula_pi ⟨e, he.toDAdm, hval⟩

theorem three_le_degree_of_formula_total_pi {D : ℕ}
    {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)} (he : TotalDAdmUπ D e)
    (hval : Expr.eval thAuπ thBuπ rhoUπ e = q22πU) : 3 ≤ D :=
  three_le_degree_of_formula_pi he.toDAdm hval

theorem no_degree_two_formula_total_pi_coalescent {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), TotalDAdmUπ 2 e
        ∧ Expr.eval thAuπ thBuπ rhoUπ e = q s22 := by
  rw [eq_q22πU_of_isSolutionUπ hq]
  exact no_degree_two_formula_total_pi

theorem three_le_degree_of_formula_total_pi_coalescent
    {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) {D : ℕ}
        {e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi)}
    (he : TotalDAdmUπ D e) (hval : Expr.eval thAuπ thBuπ rhoUπ e = q s22) : 3 ≤ D :=
  three_le_degree_of_formula_pi he.toDAdm (hval.trans (eq_q22πU_of_isSolutionUπ hq))

end Rhone.Algebra.BlockTwoSymbolic
