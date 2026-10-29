/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.TwoGameteBridge.Recursion

/-! # Equivalence of the finite recursion system and the `n = 2` solution notion -/

@[expose] public section

namespace Rhone.Algebra.TwoGameteBridge

open KilledSystem LinearAlgebra.Recursion

variable {R : Type*} [CommRing R]

def FiniteSystem (θA θB ρ : R) (πA πB : Fin 2 → R) (q : St → R) : Prop :=
  (∀ s ∈ recStates, lhsC θA θB ρ s * q s =
    rhsC 1 (θA * πA 0) (θA * πA 1) (θB * πB 0) (θB * πB 1) ρ q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC (πA 0) (πA 1) (πB 0) (πB 1) s)

theorem finiteSystem_of_isSolution {θA θB ρ : R} {πA πB : Fin 2 → R}
    {Q : Config 2 2 → R} (hQ : LinearAlgebra.Recursion.IsSolution θA θB ρ πA πB Q) :
    FiniteSystem θA θB ρ πA πB (fun s => Q (toConfig s)) := by
  constructor
  · intro s hs
    have hn : 2 ≤ s.n :=
      (KilledSystem.mem_recStates s (KilledSystem.recStates_subset s hs)).mp hs
    have h := hQ.recursion (toConfig s) (by simpa only [n_toConfig] using hn)
    rw [diag_toConfig, rhs_restrict] at h
    exact h
  · intro s hs
    have hA (i : Fin 2) : Q (toConfig (ofConfig (Config.eA i))) = πA i := by
      simpa only [toConfig_ofConfig] using hQ.bdryA i
    have hB (i : Fin 2) : Q (toConfig (ofConfig (Config.eB i))) = πB i := by
      simpa only [toConfig_ofConfig] using hQ.bdryB i
    have hC (i j : Fin 2) : Q (toConfig (ofConfig (Config.eC i j))) = πA i * πB j := by
      simpa only [toConfig_ofConfig] using hQ.bdryC i j
    simp only [bdryStates, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [bdryC, ofConfig, Config.eA, incf] using hA 0
      | simpa [bdryC, ofConfig, Config.eA, incf] using hA 1
      | simpa [bdryC, ofConfig, Config.eB, incf] using hB 0
      | simpa [bdryC, ofConfig, Config.eB, incf] using hB 1
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 0 0
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 0 1
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 1 0
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 1 1

theorem recursion_of_finiteSystem {θA θB ρ : R} {πA πB : Fin 2 → R} {q : St → R}
    (hq : FiniteSystem θA θB ρ πA πB q) (ξ : Config 2 2)
    (hA : ξ.nA ≤ 2) (hB : ξ.nB ≤ 2) (hn : 2 ≤ ξ.n) :
    diag θA θB ρ ξ * q (ofConfig ξ) =
      rhs θA θB ρ πA πB (fun ξ => q (ofConfig ξ)) ξ := by
  have hA' : (ofConfig ξ).nA ≤ 2 := by
    simpa only [← nA_toConfig (ofConfig ξ), toConfig_ofConfig] using hA
  have hB' : (ofConfig ξ).nB ≤ 2 := by
    simpa only [← nB_toConfig (ofConfig ξ), toConfig_ofConfig] using hB
  have hn' : 2 ≤ (ofConfig ξ).n := by
    simpa only [← n_toConfig (ofConfig ξ), toConfig_ofConfig] using hn
  have hc : ofConfig ξ ∈ closureList := KilledSystem.mem_closureList_iff.mpr
    ⟨hA', hB', by
      simp only [St.n, St.nA, St.nB, St.t] at hn' ⊢
      omega⟩
  have hr : ofConfig ξ ∈ recStates := (KilledSystem.mem_recStates _ hc).mpr hn'
  have h := hq.1 (ofConfig ξ) hr
  simpa only [← diag_toConfig, ← rhs_toConfig, toConfig_ofConfig] using h

structure N2IsSolution (θA θB ρ : R) (πA πB : Fin 2 → R)
    (Q : Config 2 2 → R) : Prop where
  bdryA : ∀ i, Q (Config.eA i) = πA i
  bdryB : ∀ j, Q (Config.eB j) = πB j
  bdryC : ∀ i j, Q (Config.eC i j) = πA i * πB j
  recursion : ∀ ξ, ξ.nA ≤ 2 → ξ.nB ≤ 2 → 2 ≤ ξ.n →
    diag θA θB ρ ξ * Q ξ = rhs θA θB ρ πA πB Q ξ

theorem n2IsSolution_of_finiteSystem {θA θB ρ : R} {πA πB : Fin 2 → R} {q : St → R}
    (hq : FiniteSystem θA θB ρ πA πB q) :
    N2IsSolution θA θB ρ πA πB (fun ξ => q (ofConfig ξ)) := by
  constructor
  · intro i
    have hs : ofConfig (Config.eA i) ∈ bdryStates := by
      fin_cases i <;> decide
    have h := hq.2 _ hs
    fin_cases i <;> simpa [bdryC, ofConfig, Config.eA, incf] using h
  · intro j
    have hs : ofConfig (Config.eB j) ∈ bdryStates := by
      fin_cases j <;> decide
    have h := hq.2 _ hs
    fin_cases j <;> simpa [bdryC, ofConfig, Config.eB, incf] using h
  · intro i j
    have hs : ofConfig (Config.eC i j) ∈ bdryStates := by
      fin_cases i <;> fin_cases j <;> decide
    have h := hq.2 _ hs
    fin_cases i <;> fin_cases j <;>
      simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using h
  · exact recursion_of_finiteSystem hq

theorem finiteSystem_of_n2IsSolution {θA θB ρ : R} {πA πB : Fin 2 → R}
    {Q : Config 2 2 → R} (hQ : N2IsSolution θA θB ρ πA πB Q) :
    FiniteSystem θA θB ρ πA πB (fun s => Q (toConfig s)) := by
  constructor
  · intro s hs
    have hn : 2 ≤ s.n :=
      (KilledSystem.mem_recStates s (KilledSystem.recStates_subset s hs)).mp hs
    have hc := KilledSystem.closureList_inClosure s (KilledSystem.recStates_subset s hs)
    have h := hQ.recursion (toConfig s)
      (by simpa only [nA_toConfig] using hc.1)
      (by simpa only [nB_toConfig] using hc.2.1)
      (by simpa only [n_toConfig] using hn)
    rw [diag_toConfig, rhs_restrict] at h
    exact h
  · intro s hs
    have hA (i : Fin 2) : Q (toConfig (ofConfig (Config.eA i))) = πA i := by
      simpa only [toConfig_ofConfig] using hQ.bdryA i
    have hB (i : Fin 2) : Q (toConfig (ofConfig (Config.eB i))) = πB i := by
      simpa only [toConfig_ofConfig] using hQ.bdryB i
    have hC (i j : Fin 2) : Q (toConfig (ofConfig (Config.eC i j))) = πA i * πB j := by
      simpa only [toConfig_ofConfig] using hQ.bdryC i j
    simp only [bdryStates, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [bdryC, ofConfig, Config.eA, incf] using hA 0
      | simpa [bdryC, ofConfig, Config.eA, incf] using hA 1
      | simpa [bdryC, ofConfig, Config.eB, incf] using hB 0
      | simpa [bdryC, ofConfig, Config.eB, incf] using hB 1
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 0 0
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 0 1
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 1 0
      | simpa [bdryC, ofConfig, Config.eC, Config.incC, incf] using hC 1 1
theorem finiteSystem_iff_n2IsSolution {θA θB ρ : R} {πA πB : Fin 2 → R}
    {q : St → R} : FiniteSystem θA θB ρ πA πB q ↔
      N2IsSolution θA θB ρ πA πB (fun ξ => q (ofConfig ξ)) := by
  constructor
  · exact n2IsSolution_of_finiteSystem
  · intro h
    simpa only [ofConfig_toConfig] using finiteSystem_of_n2IsSolution h

theorem restrict_finiteSystem_iff_n2IsSolution {θA θB ρ : R} {πA πB : Fin 2 → R}
    {Q : Config 2 2 → R} : FiniteSystem θA θB ρ πA πB (fun s => Q (toConfig s)) ↔
      N2IsSolution θA θB ρ πA πB Q := by
  simpa only [toConfig_ofConfig] using
    (finiteSystem_iff_n2IsSolution (q := fun s => Q (toConfig s)))

end Rhone.Algebra.TwoGameteBridge
