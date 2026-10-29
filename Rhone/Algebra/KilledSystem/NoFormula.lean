/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Solution
public import Rhone.Algebra.KilledSystem.Unique
public import Rhone.Algebra.KilledSystem.Transcription
public import Rhone.Algebra.NoDegreeOneFormula

/-! # No degree-one formula for `q22` as the solution of the killed-PIM system -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open Polynomial

def s22 : St := ⟨0, 0, 0, 0, 0, 0, 0, 2⟩

theorem s22_mem_closureList : s22 ∈ closureList := by decide

theorem s22_inClosure : s22.InClosure := by decide

theorem Val_s22_cert : Val s22 * Dq = Nq * Dcom := by
  apply mul_left_cancel₀ (by norm_num : (4 : P) ≠ 0)
  calc
    4 * (Val s22 * Dq) = (4 * Val s22) * Dq := by ring
    _ = (3 * Nq) * Dq := by rw [s22, Val_46, V46_transcription_scale]
    _ = Nq * (3 * Dq) := by ring
    _ = Nq * (4 * Dcom) := by rw [Dcom_transcription_scale]
    _ = 4 * (Nq * Dcom) := by ring

theorem qSol_s22 : qSol s22 = q22 := by
  have hDq : algebraMap P L Dq ≠ 0 := algebraMap_ne_zero Dq_ne_zero
  have hDc : algebraMap P L Dcom ≠ 0 := Dcom_L_ne_zero
  have h := congrArg (algebraMap P L) Val_s22_cert
  rw [map_mul, map_mul] at h
  have e : algebraMap P L (Val s22) * (algebraMap P L Dcom)⁻¹ * algebraMap P L Dq
      = algebraMap P L (Val s22) * algebraMap P L Dq * (algebraMap P L Dcom)⁻¹ := by ring
  rw [qSol, q22, eq_div_iff hDq, e, h, mul_inv_cancel_right₀ hDc]

theorem eq_q22_of_isSolution {q : St → L} (hq : IsSolution q) : q s22 = q22 :=
  (unique_of_isSolution hq qSol_isSolution s22 s22_mem_closureList).trans qSol_s22

theorem exists_unique_isSolution :
    IsSolution qSol ∧ ∀ q : St → L, IsSolution q → ∀ s ∈ closureList, q s = qSol s :=
  ⟨qSol_isSolution, fun _q hq => unique_of_isSolution hq qSol_isSolution⟩

theorem no_degree_one_formula_coalescent {q : St → L} (hq : IsSolution q) :
    ¬ ∃ e : Expr Fuv, DAdm thA thB rhoL 1 e ∧ Expr.eval thA thB rhoL e = q s22 := by
  rw [eq_q22_of_isSolution hq]
  exact no_degree_one_formula

theorem two_le_degree_of_formula_coalescent {q : St → L} (hq : IsSolution q) {D : ℕ} {e : Expr Fuv}
    (he : DAdm thA thB rhoL D e) (hval : Expr.eval thA thB rhoL e = q s22) : 2 ≤ D :=
  two_le_degree_of_formula he (hval.trans (eq_q22_of_isSolution hq))

end Rhone.Algebra.KilledSystem
