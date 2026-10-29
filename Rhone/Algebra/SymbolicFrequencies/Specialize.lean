/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SymbolicFrequencies.Q22
public import Rhone.Algebra.Q22

/-! # Specializing symbolic `q22` to `π_A = 1/3`, `π_B = 2/5` gives the fixed-frequency `q22` -/

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

noncomputable def pA0 : _root_.Rhone.Algebra.Fuv := 1 / 3

noncomputable def pB0 : _root_.Rhone.Algebra.Fuv := 2 / 5

noncomputable def NqSp : _root_.Rhone.Algebra.P :=
  NqOf _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0

noncomputable def DqSp : _root_.Rhone.Algebra.P :=
  DqOf _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0

noncomputable def q22Sp : _root_.Rhone.Algebra.L :=
  q22Of _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0

theorem qN2_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * ((pA0 - 1) * (pB0 - 1) * qM2 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0)
      = _root_.Rhone.Algebra.qN2 := by
  simp only [qM2, pA0, pB0, _root_.Rhone.Algebra.qN2]
  ring

theorem qN1_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * ((pA0 - 1) * (pB0 - 1) * qM1 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0)
      = _root_.Rhone.Algebra.qN1 := by
  simp only [qM1, pA0, pB0, _root_.Rhone.Algebra.qN1]
  ring

theorem qN0_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * ((pA0 - 1) * (pB0 - 1) * qM0 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0)
      = _root_.Rhone.Algebra.qN0 := by
  simp only [qM0, pA0, pB0, _root_.Rhone.Algebra.qN0]
  ring

theorem qD2_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * qD2 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0 = _root_.Rhone.Algebra.qD2 := by
  simp only [qD2, _root_.Rhone.Algebra.qD2]
  ring

theorem qD1_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * qD1 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0 = _root_.Rhone.Algebra.qD1 := by
  simp only [qD1, _root_.Rhone.Algebra.qD1]
  ring

theorem qD0_spec : (75 : _root_.Rhone.Algebra.Fuv)
    * qD0 _root_.Rhone.Algebra.uu _root_.Rhone.Algebra.vv pA0 pB0 = _root_.Rhone.Algebra.qD0 := by
  simp only [qD0, _root_.Rhone.Algebra.qD0]
  ring

theorem NqSp_eq : C (75 : _root_.Rhone.Algebra.Fuv) * NqSp = _root_.Rhone.Algebra.Nq := by
  simp only [NqSp, NqOf, MqOf, _root_.Rhone.Algebra.Nq]
  rw [← qN2_spec, ← qN1_spec, ← qN0_spec]
  simp only [map_mul, map_sub, map_ofNat, map_one]
  ring

theorem DqSp_eq : C (75 : _root_.Rhone.Algebra.Fuv) * DqSp = _root_.Rhone.Algebra.Dq := by
  simp only [DqSp, DqOf, _root_.Rhone.Algebra.Dq]
  rw [← qD2_spec, ← qD1_spec, ← qD0_spec]
  simp only [map_mul, map_ofNat]
  ring

theorem c75_ne_zero : (C (75 : _root_.Rhone.Algebra.Fuv) : _root_.Rhone.Algebra.P) ≠ 0 := by
  simp only [ne_eq, Polynomial.C_eq_zero]
  norm_num

theorem q22Sp_eq : q22Sp = _root_.Rhone.Algebra.q22 := by
  have hq : q22Sp = algebraMap _root_.Rhone.Algebra.P _root_.Rhone.Algebra.L NqSp
      / algebraMap _root_.Rhone.Algebra.P _root_.Rhone.Algebra.L DqSp := rfl
  rw [hq, _root_.Rhone.Algebra.q22, ← NqSp_eq, ← DqSp_eq, map_mul, map_mul,
    mul_div_mul_left _ _ (_root_.Rhone.Algebra.algebraMap_ne_zero c75_ne_zero)]

theorem q22π_eq_q22Of : q22π = q22Of (GenericField.uu Kpi) (GenericField.vv Kpi) piAF piBF := rfl

end Rhone.Algebra.SymbolicFrequencies
