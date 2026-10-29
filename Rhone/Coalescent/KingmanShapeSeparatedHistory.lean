/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryProjection
/-! # Histories separated by two disjoint subtree leaf-label ranges -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def sumLeftForest {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) : Finset (Finset L) :=
  forestPreimage Function.Embedding.inl
    (W.filter (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl))
noncomputable def sumRightForest {L M : Type*} [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) : Finset (Finset M) :=
  forestPreimage Function.Embedding.inr
    (W.filter (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr))
def SumPureForest {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (W : Finset (Finset (L ⊕ M))) : Prop :=
  ∀ C ∈ W, C ⊆ (univ : Finset L).map Function.Embedding.inl ∨
    C ⊆ (univ : Finset M).map Function.Embedding.inr
def SeparatedForestHistory {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (a b : ℕ) :=
  {h : Combinatorics.RankedForestHistory
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) (a+b) //
    (∀ k ≤ a+b, SumPureForest (Combinatorics.historyAt _ (a+b) h k)) ∧
    (ADR11.roots (sumLeftForest (Combinatorics.historyEnd _ (a+b) h))).card + a =
        (ADR11.roots F).card ∧
    (ADR11.roots (sumRightForest (Combinatorics.historyEnd _ (a+b) h))).card + b =
        (ADR11.roots H).card}
end Rhone.Coalescent
