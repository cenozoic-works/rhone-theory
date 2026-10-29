/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanTopologyProbability

/-! # A three-leaf counterexample to the clade-size formula for topology probabilities -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
def counterexampleHierarchy : Finset (Finset (Fin 3)) :=
  {univ, {0, 1}, {0}, {1}, {2}}

theorem counterexampleHierarchy_binary : ADR11.IsBinaryHierarchy counterexampleHierarchy := by
  unfold ADR11.IsBinaryHierarchy ADR11.IsHierarchy
  decide

theorem cladeSizeProduct_counterexampleHierarchy :
    (∏ C ∈ counterexampleHierarchy.filter (fun C => 2 ≤ C.card), C.card - 1) = 5 := by
  decide

theorem cladeSizeFormula_counterexampleHierarchy :
    (2 : ℝ) ^ (3 - 1 : ℕ) / ((3 : ℕ).factorial *
      ((∏ C ∈ counterexampleHierarchy.filter (fun C => 2 ≤ C.card),
        C.card - 1 : ℕ) : ℝ)) = 2 / 15 := by
  rw [cladeSizeProduct_counterexampleHierarchy]
  norm_num

theorem coalescent_clade_product_three :
    coalescentTopologyCladeProduct (⟨counterexampleHierarchy, counterexampleHierarchy_binary⟩ :
      LabelledTopology 3) = 2 := by
  decide

theorem topologyWeight_counterexampleHierarchy :
    topologyWeight 3 ⟨counterexampleHierarchy, counterexampleHierarchy_binary⟩ = 1 / 3 := by
  rw [kingman_topology_probability_of_clade_factors 3 (by omega), coalescent_clade_product_three]
  norm_num

theorem not_forall_topologyWeight_eq_cladeSizeFormula :
    ¬∀ (n : ℕ) (_hn : 1 ≤ n) (T : LabelledTopology n),
      topologyWeight n T =
        (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) *
          ((∏ C ∈ T.1.filter (fun C => 2 ≤ C.card), C.card - 1 : ℕ) : ℝ)) := by
  intro h
  have he := h 3 (by omega) ⟨counterexampleHierarchy, counterexampleHierarchy_binary⟩
  rw [topologyWeight_counterexampleHierarchy, cladeSizeFormula_counterexampleHierarchy] at he
  norm_num at he
end Rhone.Coalescent
