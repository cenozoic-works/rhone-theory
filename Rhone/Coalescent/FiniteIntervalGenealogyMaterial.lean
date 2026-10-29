/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogy
public import Rhone.Coalescent.SmcSupport.Material
public import Mathlib.Tactic.Linarith

/-! # Half-open interval membership under lineage splitting and merging -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport

def materialContains (a : Material) (q : ℝ) : Prop :=
  ∃ i, (a.2 i).1 ≤ q ∧ q < (a.2 i).2

theorem materialContains_merge (a b : Material) (q : ℝ) :
    materialContains (mergeMaterial a b) q ↔ materialContains a q ∨ materialContains b q := by
  constructor
  · rintro ⟨i, hi⟩
    unfold mergeMaterial at hi
    dsimp at hi
    split_ifs at hi with h
    · exact Or.inl ⟨_, hi⟩
    · exact Or.inr ⟨_, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨⟨i.val, by change i.val < a.1 + b.1 + 1 + 1; omega⟩,
        by simpa only [mergeMaterial_left_atom] using hi⟩
    · exact ⟨⟨a.1 + 1 + i.val, by change a.1 + 1 + i.val < a.1 + b.1 + 1 + 1; omega⟩,
        by simpa only [mergeMaterial_right_atom] using hi⟩

theorem materialContains_split_left (a : Material) (x q : ℝ) :
    materialContains (splitMaterial a x).1 q ↔ materialContains a q ∧ q < x := by
  constructor
  · rintro ⟨i, hlo, hhi⟩
    change (a.2 i).1 ≤ q at hlo
    change q < max (a.2 i).1 (min (a.2 i).2 x) at hhi
    have hmin : q < min (a.2 i).2 x := by
      by_contra hh
      exact (not_lt_of_ge (max_le hlo (le_of_not_gt hh))) hhi
    exact ⟨⟨i, hlo, hmin.trans_le (min_le_left _ _)⟩,
      hmin.trans_le (min_le_right _ _)⟩
  · rintro ⟨⟨i, hlo, hhi⟩, hx⟩
    exact ⟨i, hlo, (lt_min hhi hx).trans_le (le_max_right _ _)⟩

theorem materialContains_split_right (a : Material) (x q : ℝ) :
    materialContains (splitMaterial a x).2 q ↔ materialContains a q ∧ x ≤ q := by
  constructor
  · rintro ⟨i, hlo, hhi⟩
    change max (a.2 i).1 (min (a.2 i).2 x) ≤ q at hlo
    change q < (a.2 i).2 at hhi
    have hmin : min (a.2 i).2 x ≤ q := (le_max_right _ _).trans hlo
    have hx : x ≤ q := by
      by_contra hh
      exact (not_lt_of_ge hmin) (lt_min hhi (lt_of_not_ge hh))
    exact ⟨⟨i, (le_max_left _ _).trans hlo, hhi⟩, hx⟩
  · rintro ⟨⟨i, hlo, hhi⟩, hx⟩
    exact ⟨i, max_le hlo ((min_le_right _ _).trans hx), hhi⟩

theorem initial_materialContains (N : ℕ) (i : Fin N) (q : ℝ) :
    materialContains ((initialState N).2.2.2 i).2 q ↔ 0 ≤ q ∧ q < 1 := by
  constructor
  · rintro ⟨j, hj⟩
    exact hj
  · intro hq
    exact ⟨0, hq⟩

end Rhone.Coalescent.IntervalProcess
