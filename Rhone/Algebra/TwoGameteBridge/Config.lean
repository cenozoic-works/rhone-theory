/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Recursion
public import Rhone.LinearAlgebra.Recursion.Defs

/-! # The explicit biallelic state is the general configuration type -/

@[expose] public section

namespace Rhone.Algebra.TwoGameteBridge

open KilledSystem LinearAlgebra.Recursion

def toConfig (s : St) : Config 2 2 :=
  ⟨![s.a0, s.a1], ![s.b0, s.b1], ![![s.c00, s.c01], ![s.c10, s.c11]]⟩

def ofConfig (ξ : Config 2 2) : St :=
  ⟨ξ.a 0, ξ.a 1, ξ.b 0, ξ.b 1, ξ.c 0 0, ξ.c 0 1, ξ.c 1 0, ξ.c 1 1⟩

@[simp] theorem ofConfig_toConfig (s : St) : ofConfig (toConfig s) = s := by
  cases s
  rfl

@[simp] theorem toConfig_ofConfig (ξ : Config 2 2) : toConfig (ofConfig ξ) = ξ := by
  apply Config.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

def configEquiv : St ≃ Config 2 2 :=
  ⟨toConfig, ofConfig, ofConfig_toConfig, toConfig_ofConfig⟩

@[simp] theorem t_toConfig (s : St) : (toConfig s).t = s.t := by
  simp [toConfig, Config.t, St.t, Fin.sum_univ_two]
  omega

@[simp] theorem nA_toConfig (s : St) : (toConfig s).nA = s.nA := by
  simp [Config.nA, Config.sumA, Config.t, toConfig, St.nA, St.t, Fin.sum_univ_two]
  omega

@[simp] theorem nB_toConfig (s : St) : (toConfig s).nB = s.nB := by
  simp [Config.nB, Config.sumB, Config.t, toConfig, St.nB, St.t, Fin.sum_univ_two]
  omega

@[simp] theorem n_toConfig (s : St) : (toConfig s).n = s.n := by
  simp [Config.n, Config.sumA, Config.sumB, Config.t, toConfig, St.n, St.t,
    Fin.sum_univ_two]
  omega

theorem mem_closureList_iff (s : St) : s ∈ closureList ↔
    (toConfig s).nA ≤ 2 ∧ (toConfig s).nB ≤ 2 ∧
      1 ≤ (toConfig s).nA + (toConfig s).nB := by
  simpa only [nA_toConfig, nB_toConfig, St.InClosure] using KilledSystem.mem_closureList_iff
      (s := s)

end Rhone.Algebra.TwoGameteBridge
