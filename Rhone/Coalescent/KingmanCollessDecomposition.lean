/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanCollessSplit
/-!
# Sum Colless endpoint payoffs over the two complementary root sides

Source: cardona2013balance, §7. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
theorem colless_payoff_sum_root_splits (n : ℕ) (hn : 2 ≤ n) :
    (∑ A : Finset (Fin n), Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0)) =
    2 * Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
        (fun G => (treeColless G : ℝ)) := by
  classical
  unfold Combinatorics.historyPayoff
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro h hh
  let G := Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h
  have hG : ADR11.IsBinaryHierarchy G := Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h
  have hterm : (∑ A : Finset (Fin n),
      if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0) =
      2 * (treeColless G : ℝ) := by
    simp_rw [root_split_iff_root_child G hG (by simpa using hn)]
    rw [← sum_filter]
    have hf : (univ : Finset (Finset (Fin n))).filter
        (fun A => A ∈ ADR11.roots (G.erase univ)) = ADR11.roots (G.erase univ) := by
      ext A
      simp
    rw [hf, sum_const, nsmul_eq_mul]
    obtain ⟨A, ha, hb, hs⟩ := binary_hierarchy_root_pair G hG (by simpa using hn)
    have hab : A ≠ univ \ A := by
      obtain ⟨x, hx⟩ := ha
      intro he
      exact (mem_sdiff.mp (he ▸ hx)).2 hx
    rw [hs, card_pair hab]
    norm_num
  change (∑ A : Finset (Fin n), Combinatorics.historyMass (ADR11.singletonForest n) (n - 1) h *
      (if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0)) = _
  rw [← mul_sum, hterm]
  ring
end Rhone.Coalescent
