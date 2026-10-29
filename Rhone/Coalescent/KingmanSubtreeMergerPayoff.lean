/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanSubtreePayoff
/-!
# First-merger payoff sums in chronological Kingman histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sum_merges_history_payoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (f : Finset (Finset L) → ℝ) :
    (∑ G ∈ ADR11.merges F, Combinatorics.historyPayoff G ((ADR11.roots F).card - 2) f) =
      ((ADR11.roots F).card.choose 2 : ℝ) * Combinatorics.historyPayoff F ((ADR11.roots F).card - 1)
          f := by
  by_cases hk : 2 ≤ (ADR11.roots F).card
  · rw [show (ADR11.roots F).card - 1 = ((ADR11.roots F).card - 2) + 1 by omega,
      Combinatorics.history_payoff_succ]
    have hs : ∀ G ∈ ADR11.merges F,
        ADR11.jumpMatrix F G * Combinatorics.historyPayoff G ((ADR11.roots F).card - 2) f =
          ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ *
            Combinatorics.historyPayoff G ((ADR11.roots F).card - 2) f := by
      intro G hG
      rw [ADR11.jumpMatrix_apply_of_isForest (by omega), ite_eq_left hG]
    rw [sum_congr rfl hs, ← mul_sum, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)), one_mul]
  · have hc : (ADR11.roots F).card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hm : ADR11.merges F = ∅ := card_eq_zero.mp (by rw [hF.card_merges, hc])
    rw [hm, sum_empty, hc, Nat.cast_zero, zero_mul]
theorem sum_merges_within_history_payoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A) (f : Finset (Finset L) → ℝ) :
    (∑ G ∈ (ADR11.merges F).filter (fun G => ∀ C ∈ G \ F, C ⊆ A),
      Combinatorics.historyPayoff (G.filter (fun C => C ⊆ A))
        (((ADR11.roots F).filter (fun C => C ⊆ A)).card - 2) f) =
      ((((ADR11.roots F).filter (fun C => C ⊆ A)).card).choose 2 : ℝ) *
        Combinatorics.historyPayoff (F.filter (fun C => C ⊆ A))
          (((ADR11.roots F).filter (fun C => C ⊆ A)).card - 1) f := by
  rw [sum_merges_within_restrict F hF A hpure
    (fun H => Combinatorics.historyPayoff H (((ADR11.roots F).filter (fun C => C ⊆ A)).card - 2) f)]
  have hS : ADR11.IsForest (F.filter (fun C => C ⊆ A)) :=
    ⟨fun C hC => hF.1 C (mem_filter.mp hC).1,
      fun C hC D hD => hF.2 C (mem_filter.mp hC).1 D (mem_filter.mp hD).1⟩
  simpa only [roots_within_pure_forest F hF A hpure] using
    sum_merges_history_payoff (F.filter (fun C => C ⊆ A)) hS f
end Rhone.Coalescent
