/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSubtreeFactorization
public import Rhone.Coalescent.KingmanHistoryEmbedding
public import Rhone.Coalescent.KingmanRootReconstruction
public import Rhone.Coalescent.KingmanSingletonEmbedding
public import Rhone.Coalescent.KingmanRootPair

/-!
# Topology probability in the complete Kingman history law

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
abbrev LabelledTopology (n : ℕ) :=
  {G : Finset (Finset (Fin n)) // ADR11.IsBinaryHierarchy G}

noncomputable def topologyWeight (n : ℕ) (T : LabelledTopology n) : ℝ :=
  Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => if G = T.1 then 1 else 0)

def coalescentTopologyCladeProduct {n : ℕ} (T : LabelledTopology n) : ℕ :=
  ∏ C ∈ T.1.filter (fun C => 2 ≤ C.card), (C.card - 1)

theorem topology_one_singletonForest (T : LabelledTopology 1) :
    T.1 = ADR11.singletonForest 1 := by
  classical
  have hs : ADR11.singletonForest 1 = {(univ : Finset (Fin 1))} := by
    simp [ADR11.singletonForest]
  rw [hs]
  ext C
  constructor
  · intro hc
    apply mem_singleton.mpr
    have hp := card_pos.mpr (T.2.1.2.2.1 C hc)
    have hl := card_le_univ C
    have he : C.card = Fintype.card (Fin 1) := by simp only [Fintype.card_fin] at *; omega
    exact eq_univ_of_card C he
  · intro hc
    rw [mem_singleton.mp hc]
    exact T.2.1.1

theorem kingman_topology_probability_of_clade_factors_one (T : LabelledTopology 1) :
    topologyWeight 1 T = (2 : ℝ) ^ (1 - 1 : ℕ) /
      ((1 : ℕ).factorial * (coalescentTopologyCladeProduct T : ℝ)) := by
  have hT := topology_one_singletonForest T
  have hprod : coalescentTopologyCladeProduct T = 1 := by
    simp [coalescentTopologyCladeProduct, hT, ADR11.singletonForest]
  rw [hprod]
  norm_num
  unfold topologyWeight Combinatorics.historyPayoff
  change (∑ h : PUnit, (1 : ℝ) * (if ADR11.singletonForest 1 = T.1 then 1 else 0)) = 1
  simp [hT]
end Rhone.Coalescent
