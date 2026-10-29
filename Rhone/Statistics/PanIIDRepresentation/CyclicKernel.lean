/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.TripleKernel

/-! # A deterministic cyclic decomposition of the three-sample order kernel -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.PanIIDRepresentation
open AtomicRank

def selectedKernel (φ : ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  if min a b < c then φ (min a b) c else 0

theorem cyclic_selected_ordered (φ : ℝ → ℝ → ℝ) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) :
    selectedKernel φ a b c + selectedKernel φ b c a + selectedKernel φ c a b =
      φ a b + φ a c := by
  simp only [selectedKernel, min_eq_left hab.le, min_eq_left hbc.le,
    min_eq_right (hab.trans hbc).le, ite_eq_left (hab.trans hbc),
    ite_eq_right (not_lt_of_ge hab.le), ite_eq_left hab]
  ring

lemma sortedKernel_first_max (f : Coefficients) {a b c : ℝ}
    (hba : b ≤ a) (hca : c ≤ a) :
    sortedKernel f a b c = (value f a b + value f a c) / 2 := by
  unfold sortedKernel
  rw [max_eq_left (max_le hba hca), min_eq_right (min_le_left b c |>.trans hba)]
  rcases le_total b c with h | h
  · simp only [min_eq_left h]
    rw [show a + b + c - a - b = c by ring]
  · simp only [min_eq_right h]
    rw [show a + b + c - a - c = b by ring]
    ring

theorem sortedKernel_cyclic (f : Coefficients) (g : ℝ → ℝ) (hg : Antitone g)
    {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sortedKernel f (g a) (g b) (g c) =
      (selectedKernel (fun x y => value f (g x) (g y)) a b c +
        selectedKernel (fun x y => value f (g x) (g y)) b c a +
        selectedKernel (fun x y => value f (g x) (g y)) c a b) / 2 := by
  rcases lt_or_gt_of_ne hab with hab | hab <;>
    rcases lt_or_gt_of_ne hbc with hbc | hbc <;>
      rcases lt_or_gt_of_ne hac with hac | hac
  all_goals try (exfalso; linarith)
  all_goals
    have habg := hg (le_of_lt hab)
    have hbcg := hg (le_of_lt hbc)
    have hacg := hg (le_of_lt hac)
    simp only [selectedKernel, sortedKernel]
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      le_of_lt, not_lt_of_ge, ite_true, ite_false]
    ring_nf

end Rhone.Statistics.PanIIDRepresentation
