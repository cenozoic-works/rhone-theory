/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSampler
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Linarith

/-! # Positivity of selected actions under the cumulative-rate selector -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem chooseByRate_exists_positive {α : Type*} (rate : α → ℝ)
    (l : List α) (hr : ∀ a ∈ l, 0 ≤ rate a) (u : ℝ)
    (hu : 0 ≤ u) (hlt : u < (l.map rate).sum) :
    ∃ a, chooseByRate rate l u = some a ∧ 0 < rate a := by
  induction l generalizing u with
  | nil => simp only [List.map_nil, List.sum_nil] at hlt; linarith
  | cons a l ih =>
    by_cases ha : u < rate a
    · exact ⟨a, by simp [chooseByRate, ha], by linarith⟩
    · have hu' : 0 ≤ u - rate a := by linarith
      have hlt' : u - rate a < (l.map rate).sum := by
        simp only [List.map_cons, List.sum_cons] at hlt
        linarith
      obtain ⟨b, hb, hpos⟩ := ih (fun b hb => hr b (by simp [hb])) _ hu' hlt'
      exact ⟨b, by simpa [chooseByRate, ha] using hb, hpos⟩

theorem selectedAction_exists_positive (mode : Mode) (R : ℝ) (s : State)
    (u : Noise) (hu0 : 0 ≤ u 0) (hu1 : u 0 < 1)
    (ht : 0 < totalRate mode R s) :
    ∃ a, selectedAction mode R s u = some a ∧ 0 < candidateRate mode R s a := by
  classical
  have hsum : (Finset.univ.toList.map
      (fun a : ActionIndex s => (candidateRate mode R s a : ℝ))).sum =
      (totalRate mode R s : ℝ) := by
    simp [totalRate]
  have ht' : 0 < (totalRate mode R s : ℝ) := by exact_mod_cast ht
  obtain ⟨a, ha, hp⟩ := chooseByRate_exists_positive
    (fun a : ActionIndex s => (candidateRate mode R s a : ℝ)) Finset.univ.toList
    (fun a _ => (candidateRate mode R s a).property)
    (u 0 * (totalRate mode R s : ℝ)) (mul_nonneg hu0 ht'.le)
    (by rw [hsum]; nlinarith)
  exact ⟨a, ha, by exact_mod_cast hp⟩

theorem positive_pair_order (mode : Mode) (R : ℝ) (s : State)
    (ij : Fin s.2.2.1 × Fin s.2.2.1)
    (h : 0 < candidateRate mode R s (.inl ij)) : ij.1.val < ij.2.val := by
  classical
  unfold candidateRate at h
  dsimp only at h
  split_ifs at h with hc
  · exact hc.1
  · simp at h

theorem unrestricted_totalRate_positive (R : ℝ) (s : State)
    (hm : 2 ≤ s.2.2.1) : 0 < totalRate false R s := by
  classical
  let i : Fin s.2.2.1 := ⟨0, by omega⟩
  let j : Fin s.2.2.1 := ⟨1, by omega⟩
  have hc : candidateRate false R s (.inl (i, j)) = 1 := by
    simp [candidateRate, i, j]
  have hle : candidateRate false R s (.inl (i, j)) ≤ totalRate false R s :=
    Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ _)
  rw [hc] at hle
  exact lt_of_lt_of_le (by norm_num) hle

end Rhone.Coalescent.SmcSupport
