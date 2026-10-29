/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanCollessSubtree
/-!
# Split-supported Colless expectation from subtree history laws

Source: cardona2013balance, §7; kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem splitHistoryPayoff_compl {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A : Finset L) (f g : Finset (Finset L) → ℝ) :
    splitHistoryPayoff F A f g = splitHistoryPayoff F (univ \ A) g f := by
  have hc : univ \ (univ \ A) = A := by ext x; simp
  unfold splitHistoryPayoff Combinatorics.historyPayoff
  rw [hc, pair_comm]
  apply sum_congr rfl
  intro h hh
  dsimp only
  split_ifs <;> ring
/-- Source: cardona2013balance, §7. -/
theorem colless_root_split_payoff (n a b : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin n)) (hA : A.Nonempty) (hB : (univ \ A).Nonempty)
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (he : (univ : Finset (Fin a)).map e = A)
    (hf : (univ : Finset (Fin b)).map f = univ \ A) :
    Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0) =
    rootSplitMass n A *
      (Combinatorics.historyPayoff (ADR11.singletonForest a) (a - 1)
          (fun G => (treeColless G : ℝ)) +
       Combinatorics.historyPayoff (ADR11.singletonForest b) (b - 1)
           (fun G => (treeColless G : ℝ)) +
       ((max A.card (univ \ A).card - min A.card (univ \ A).card : ℕ) : ℝ)) := by
  let d : ℝ := ((max A.card (univ \ A).card - min A.card (univ \ A).card : ℕ) : ℝ)
  have hc : univ \ (univ \ A) = A := by ext x; simp
  have hparts : Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0) =
      splitHistoryPayoff (ADR11.singletonForest n) A (fun G => (treeColless G : ℝ)) (fun _ => 1) +
      splitHistoryPayoff (ADR11.singletonForest n) A (fun _ => 1) (fun G => (treeColless G : ℝ)) +
      rootSplitMass n A * d := by
    unfold splitHistoryPayoff rootSplitMass Combinatorics.historyPayoff
    rw [ADR11.card_roots_singletonForest, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro h hh
    dsimp only
    split_ifs with hs
    · have hd := treeColless_root_split _ (Combinatorics.historyEnd_isBinaryHierarchy n hn h) A hA
        hB hs
      have hdR := congrArg (fun z : ℕ => (z : ℝ)) hd
      simp only [Nat.cast_add] at hdR
      rw [hdR]
      dsimp [d]
      ring
    · simp
  rw [hparts, colless_split_subtree_payoff n a b A hA hB e f he hf,
    splitHistoryPayoff_compl (ADR11.singletonForest n) A
      (fun _ => 1) (fun G => (treeColless G : ℝ))]
  have hh : rootSplitMass n (univ \ A) = rootSplitMass n A := by
    unfold rootSplitMass
    rw [hc, pair_comm]
  rw [colless_split_subtree_payoff n b a (univ \ A) hB (hc.symm ▸ hA) f e hf
    (he.trans hc.symm), hh]
  dsimp [d]
  ring
end Rhone.Coalescent
