/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.ClosureLists

/-! # Membership in the fully-typed n = 2 closure -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

private theorem mem_closureList_c00_0_c01_0 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 0, 0, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 0, 0, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 2 := by omega
  have ba1 : a1 ≤ 2 := by omega
  have bb0 : b0 ≤ 2 := by omega
  have bb1 : b1 ≤ 2 := by omega
  have bc10 : c10 ≤ 2 := by omega
  have bc11 : c11 ≤ 2 := by omega
  interval_cases c10 <;> interval_cases c11 <;>
    interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    first | decide | omega

private theorem mem_closureList_c00_0_c01_1 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 0, 1, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 0, 1, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 1 := by omega
  have ba1 : a1 ≤ 1 := by omega
  have bb0 : b0 ≤ 1 := by omega
  have bb1 : b1 ≤ 1 := by omega
  have bc10 : c10 ≤ 1 := by omega
  have bc11 : c11 ≤ 1 := by omega
  interval_cases c10 <;> interval_cases c11 <;>
    interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    first | decide | omega

private theorem mem_closureList_c00_0_c01_2 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 0, 2, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 0, 2, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 0 := by omega
  have ba1 : a1 ≤ 0 := by omega
  have bb0 : b0 ≤ 0 := by omega
  have bb1 : b1 ≤ 0 := by omega
  have bc10 : c10 ≤ 0 := by omega
  have bc11 : c11 ≤ 0 := by omega
  interval_cases c10
  interval_cases c11
  interval_cases a0
  interval_cases a1
  interval_cases b0
  interval_cases b1
  decide

private theorem mem_closureList_c00_1_c01_0 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 1, 0, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 1, 0, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 1 := by omega
  have ba1 : a1 ≤ 1 := by omega
  have bb0 : b0 ≤ 1 := by omega
  have bb1 : b1 ≤ 1 := by omega
  have bc10 : c10 ≤ 1 := by omega
  have bc11 : c11 ≤ 1 := by omega
  interval_cases c10 <;> interval_cases c11 <;>
    interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    first | decide | omega

private theorem mem_closureList_c00_1_c01_1 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 1, 1, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 1, 1, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 0 := by omega
  have ba1 : a1 ≤ 0 := by omega
  have bb0 : b0 ≤ 0 := by omega
  have bb1 : b1 ≤ 0 := by omega
  have bc10 : c10 ≤ 0 := by omega
  have bc11 : c11 ≤ 0 := by omega
  interval_cases c10
  interval_cases c11
  interval_cases a0
  interval_cases a1
  interval_cases b0
  interval_cases b1
  decide

private theorem mem_closureList_c00_2_c01_0 (a0 a1 b0 b1 c10 c11 : ℕ)
    (h : (⟨a0, a1, b0, b1, 2, 0, c10, c11⟩ : St).InClosure) :
    (⟨a0, a1, b0, b1, 2, 0, c10, c11⟩ : St) ∈ closureList := by
  simp only [St.InClosure, St.nA, St.nB, St.t] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ba0 : a0 ≤ 0 := by omega
  have ba1 : a1 ≤ 0 := by omega
  have bb0 : b0 ≤ 0 := by omega
  have bb1 : b1 ≤ 0 := by omega
  have bc10 : c10 ≤ 0 := by omega
  have bc11 : c11 ≤ 0 := by omega
  interval_cases c10
  interval_cases c11
  interval_cases a0
  interval_cases a1
  interval_cases b0
  interval_cases b1
  decide

theorem mem_closureList_of_inClosure {s : St} (h : s.InClosure) : s ∈ closureList := by
  obtain ⟨a0, a1, b0, b1, c00, c01, c10, c11⟩ := s
  have hbounds := h
  simp only [St.InClosure, St.nA, St.nB, St.t] at hbounds
  have bc00 : c00 ≤ 2 := by omega
  have bc01 : c01 ≤ 2 := by omega
  interval_cases c00 <;> interval_cases c01
  all_goals first
    | exact mem_closureList_c00_0_c01_0 a0 a1 b0 b1 c10 c11 h
    | exact mem_closureList_c00_0_c01_1 a0 a1 b0 b1 c10 c11 h
    | exact mem_closureList_c00_0_c01_2 a0 a1 b0 b1 c10 c11 h
    | exact mem_closureList_c00_1_c01_0 a0 a1 b0 b1 c10 c11 h
    | exact mem_closureList_c00_1_c01_1 a0 a1 b0 b1 c10 c11 h
    | exact mem_closureList_c00_2_c01_0 a0 a1 b0 b1 c10 c11 h
    | omega

theorem mem_closureList_iff {s : St} : s ∈ closureList ↔ s.InClosure :=
  ⟨fun h => closureList_inClosure s h, mem_closureList_of_inClosure⟩

end Rhone.Algebra.KilledSystem
