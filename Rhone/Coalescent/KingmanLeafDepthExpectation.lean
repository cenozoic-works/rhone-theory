/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanLeafDepth
/-!
# Leaf-depth expectations in valid chronological Kingman histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem history_payoff_leaf_depth {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (x : L)
    (hx : x ∈ ADR11.lineages F) (t : ℕ)
    (ht : t ≤ (ADR11.roots F).card - 1) :
    Combinatorics.historyPayoff F t (fun G => (leafCladeDepth G x : ℝ)) =
      (leafCladeDepth F x : ℝ) +
        2 * ∑ j ∈ Finset.range t, (1 : ℝ) / ((ADR11.roots F).card - j : ℕ) := by
  induction t generalizing F with
  | zero =>
    unfold Combinatorics.historyPayoff
    change (∑ h : PUnit, (1 : ℝ) * (leafCladeDepth F x : ℝ)) = _
    simp
  | succ t ih =>
    have hk : 2 ≤ (ADR11.roots F).card := by omega
    have hJ : (∑ G ∈ ADR11.merges F, ADR11.jumpMatrix F G) = 1 := by
      have hp := history_payoff_one F hF 1 (by omega)
      rw [Combinatorics.history_payoff_succ] at hp
      have hs : ∀ G ∈ ADR11.merges F,
          ADR11.jumpMatrix F G * Combinatorics.historyPayoff G 0 (fun _ => (1 : ℝ)) =
              ADR11.jumpMatrix F G := by
        intro G hG
        rw [history_payoff_one G (hF.of_mem_merges hG).1 0 (by omega), mul_one]
      rw [sum_congr rfl hs] at hp
      exact hp
    have hstep : ∀ G ∈ ADR11.merges F,
        Combinatorics.historyPayoff G t (fun H => (leafCladeDepth H x : ℝ)) =
          (leafCladeDepth G x : ℝ) +
            2 * ∑ j ∈ range t, (1 : ℝ) / ((ADR11.roots F).card - 1 - j : ℕ) := by
      intro G hG
      obtain ⟨hGf, hGr, _, _, hGl⟩ := hF.of_mem_merges hG
      rw [ih G hGf (by rw [hGl]; exact hx) (by omega)]
      have he : (ADR11.roots G).card = (ADR11.roots F).card - 1 := by omega
      rw [he]
    rw [Combinatorics.history_payoff_succ]
    have hs : ∀ G ∈ ADR11.merges F,
        ADR11.jumpMatrix F G * Combinatorics.historyPayoff G t (fun H => (leafCladeDepth H x : ℝ)) =
          ADR11.jumpMatrix F G * ((leafCladeDepth G x : ℝ) +
            2 * ∑ j ∈ range t, (1 : ℝ) / ((ADR11.roots F).card - 1 - j : ℕ)) := by
      intro G hG
      rw [hstep G hG]
    rw [sum_congr rfl hs]
    simp_rw [mul_add]
    rw [sum_add_distrib, ← sum_mul, hJ, one_mul, sum_jump_leaf_depth F hF x hx hk,
      sum_range_succ']
    simp only [Nat.sub_zero]
    have hshift : (∑ j ∈ range t, (1 : ℝ) / ((ADR11.roots F).card - (j + 1) : ℕ)) =
        ∑ j ∈ range t, (1 : ℝ) / ((ADR11.roots F).card - 1 - j : ℕ) := by
      apply sum_congr rfl
      intro j hj
      congr 2
      omega
    rw [hshift]
    ring
end Rhone.Coalescent
