/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Solution
public import Rhone.Algebra.KilledSystemULast.Unique
public import Rhone.Algebra.KilledSystemULast.Transcription
public import Rhone.Algebra.KilledSystemULast.Bridge
public import Rhone.Algebra.KilledSystemULast.NoFormulaSwapped

/-! # No degree-two formula for `q22` as the solution of the `u`-last killed-PIM system -/

@[expose] public section

set_option maxSynthPendingDepth 3

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

theorem ValU_s22_cert : ValU s22 * DqU = NqU * DcomU := by
  simp only [s22, ValU_46]
  rw [VU46_transcription_scale, DcomU_transcription_scale]
  ring

theorem qSolU_s22 : qSolU s22 = q22u := by
  have hDq : algebraMap P L DqU ≠ 0 := algebraMap_ne_zero DqU_ne_zero
  have hDc : algebraMap P L DcomU ≠ 0 := DcomU_L_ne_zero
  have h := congrArg (algebraMap P L) ValU_s22_cert
  rw [map_mul, map_mul] at h
  have e : algebraMap P L (ValU s22) * (algebraMap P L DcomU)⁻¹ * algebraMap P L DqU
      = algebraMap P L (ValU s22) * algebraMap P L DqU * (algebraMap P L DcomU)⁻¹ := by ring
  rw [qSolU, q22u, eq_div_iff hDq, e, h]
  exact mul_inv_cancel_right₀ (G₀ := L) hDc _

theorem eq_q22u_of_isSolutionU {q : St → L} (hq : IsSolutionU q) : q s22 = q22u :=
  (unique_of_isSolutionU hq qSolU_isSolutionU s22 s22_mem_closureList).trans qSolU_s22

theorem exists_unique_isSolutionU :
    IsSolutionU qSolU ∧ ∀ q : St → L, IsSolutionU q → ∀ s ∈ closureList, q s = qSolU s :=
  ⟨qSolU_isSolutionU, fun _q hq => unique_of_isSolutionU hq qSolU_isSolutionU⟩

theorem no_degree_two_formula_coalescent {q : St → L} (hq : IsSolutionU q) :
    ¬ ∃ e : Expr Fuv, DAdm thAu thBu rhoU 2 e ∧ Expr.eval thAu thBu rhoU e = q s22 := by
  rw [eq_q22u_of_isSolutionU hq]
  exact no_degree_two_formula

theorem three_le_degree_of_formula_coalescent {q : St → L} (hq : IsSolutionU q) {D : ℕ}
    {e : Expr Fuv}
    (he : DAdm thAu thBu rhoU D e) (hval : Expr.eval thAu thBu rhoU e = q s22) : 3 ≤ D :=
  three_le_degree_of_formula he (hval.trans (eq_q22u_of_isSolutionU hq))

theorem no_degree_two_formula_total_coalescent {q : St → L} (hq : IsSolutionU q) :
    ¬ ∃ e : Expr Fuv, GenericField.TotalDAdmU 2 e ∧ Expr.eval thAu thBu rhoU e = q s22 := by
  rw [eq_q22u_of_isSolutionU hq]
  exact GenericField.no_degree_two_formula_total

theorem unique_auxRho (Δ : St → L)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s
      = rhsC 1 (thA * piA0) (thA * piA1) (thB * piB0) (thB * piB1) rhoL Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 :=
  unique_auxG thA thB rhoL piA0 piA1 piB0 piB1 Δ ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12
    ne_d1_21 ne_E12 ne_E21 ne_d2_22 ne_W22 ne_W4_22 ne_D22 hrec hbd

theorem three_le_degree_of_formula_total_coalescent {q : St → L} (hq : IsSolutionU q) {D : ℕ}
    {e : Expr Fuv} (he : GenericField.TotalDAdmU D e)
    (hval : Expr.eval thAu thBu rhoU e = q s22) : 3 ≤ D :=
  GenericField.three_le_degree_of_formula_total he (hval.trans (eq_q22u_of_isSolutionU hq))

end Rhone.Algebra.KilledSystemULast
