/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeInterleaving
/-!
# Each interleaving counter takes every value up to the size of its history

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
private theorem shape_counter_range (f : ℕ → ℕ) (t : ℕ) (hz : f 0 = 0)
    (hstep : ∀ k < t, f (k + 1) ≤ f k + 1) :
    ∀ j ≤ f t, ∃ k ≤ t, f k = j := by
  induction t with
  | zero =>
    intro j hj
    refine ⟨0, le_rfl, ?_⟩
    omega
  | succ t ih =>
    intro j hj
    by_cases hjt : j ≤ f t
    · obtain ⟨k, hk, he⟩ := ih (fun k hk => hstep k (by omega)) j hjt
      exact ⟨k, by omega, he⟩
    · refine ⟨t + 1, le_rfl, ?_⟩
      have := hstep t (by omega)
      omega
theorem interleavingLeft_range {a b : ℕ} (s : HistoryInterleaving a b)
    (j : ℕ) (hj : j ≤ a) : ∃ k ≤ a + b, interleavingLeft s k = j := by
  apply shape_counter_range (interleavingLeft s) (a + b) (interleaving_counts_zero s).1
  · intro k hk
    have hc := interleaving_counts_succ s ⟨k, hk⟩
    dsimp only at hc
    split at hc <;> omega
  · rw [(interleaving_counts_end s).1]
    exact hj
theorem interleavingRight_range {a b : ℕ} (s : HistoryInterleaving a b)
    (j : ℕ) (hj : j ≤ b) : ∃ k ≤ a + b, interleavingRight s k = j := by
  apply shape_counter_range (interleavingRight s) (a + b) (interleaving_counts_zero s).2
  · intro k hk
    have hc := interleaving_counts_succ s ⟨k, hk⟩
    dsimp only at hc
    split at hc <;> omega
  · rw [(interleaving_counts_end s).2]
    exact hj
end Rhone.Combinatorics
