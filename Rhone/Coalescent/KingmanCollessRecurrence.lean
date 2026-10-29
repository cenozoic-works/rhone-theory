/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanCollessDecomposition
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
/-!
# Size recurrence for Colless payoffs under labelled Kingman histories

Source: cardona2013balance, §7; kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
noncomputable def collessExpected (n : ℕ) : ℝ :=
  Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeColless G : ℝ))
private noncomputable def collessLeafEmbedding {n : ℕ} (A : Finset (Fin n)) :
    Fin A.card ↪ Fin n :=
  A.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ A))
private theorem collessLeafEmbedding_range {n : ℕ} (A : Finset (Fin n)) :
    (univ : Finset (Fin A.card)).map (collessLeafEmbedding A) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact (A.equivFin.symm y).2
  · intro hx
    refine mem_map.mpr ⟨A.equivFin ⟨x, hx⟩, mem_univ _, ?_⟩
    change (A.equivFin.symm (A.equivFin ⟨x, hx⟩)).val = x
    rw [Equiv.symm_apply_apply]
/-- Source: cardona2013balance, §7. -/
theorem colless_root_split_size_payoff (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n)) :
    Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
      (fun G => if ADR11.roots (G.erase univ) = {A, univ \ A} then (treeColless G : ℝ) else 0) =
    if 0 < A.card ∧ A.card < n then
      (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) *
        (collessExpected A.card + collessExpected (n - A.card) +
          ((max A.card (n - A.card) - min A.card (n - A.card) : ℕ) : ℝ)) else 0 := by
  classical
  have hcard : (univ \ A).card = n - A.card := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_fin]
  by_cases ha : 0 < A.card ∧ A.card < n
  · rw [ite_eq_left ha]
    have hab : (univ \ A).Nonempty := card_pos.mp (by rw [hcard]; omega)
    have hp := colless_root_split_payoff n A.card (univ \ A).card (by omega) A
      (card_pos.mp ha.1) hab (collessLeafEmbedding A) (collessLeafEmbedding (univ \ A))
      (collessLeafEmbedding_range A) (collessLeafEmbedding_range (univ \ A))
    rw [hcard, root_split_mass n hn A ha.1 ha.2] at hp
    exact hp
  · rw [ite_eq_right ha]
    unfold Combinatorics.historyPayoff
    apply sum_eq_zero
    intro h hh
    dsimp only
    have hno : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) ≠
        {A, univ \ A} := by
      intro hs
      have hG := Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h
      have hAr : A ∈ ADR11.roots
          ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
        rw [hs]
        exact mem_insert_self _ _
      have hBr : univ \ A ∈ ADR11.roots
          ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
        rw [hs]
        exact mem_insert_of_mem (mem_singleton_self _)
      have hca := card_pos.mpr (hG.1.2.2.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2)
      have hcb := card_pos.mpr (hG.1.2.2.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2)
      rw [hcard] at hcb
      exact ha ⟨hca, by omega⟩
    simp only [ite_eq_right hno, mul_zero]
/-- Source: cardona2013balance, §7. -/
theorem kingman_colless_recurrence (n : ℕ) (hn : 2 ≤ n) :
    collessExpected n = (1 : ℝ) / (n - 1 : ℕ) *
      ∑ k ∈ Ico 1 n, (collessExpected k + collessExpected (n - k) +
        ((max k (n - k) - min k (n - k) : ℕ) : ℝ)) := by
  classical
  let f : ℕ → ℝ := fun k => collessExpected k + collessExpected (n - k) +
    ((max k (n - k) - min k (n - k) : ℕ) : ℝ)
  have hbycard : ∀ k ∈ range (n + 1),
      (∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
        if 0 < A.card ∧ A.card < n then
          (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) * f A.card else 0) =
      if 0 < k ∧ k < n then (2 : ℝ) / (n - 1 : ℕ) * f k else 0 := by
    intro k hk
    have hkN : k ≤ n := by have := mem_range.mp hk; omega
    have hsize : ∀ A ∈ (univ : Finset (Fin n)).powersetCard k,
        (if 0 < A.card ∧ A.card < n then
          (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) * f A.card else 0) =
        (if 0 < k ∧ k < n then (2 : ℝ) / ((n - 1 : ℕ) * (n.choose k : ℝ)) * f k else 0) := by
      intro A hA
      rw [(mem_powersetCard.mp hA).2]
    rw [sum_congr rfl hsize, sum_const, nsmul_eq_mul, card_powersetCard,
      card_univ, Fintype.card_fin]
    by_cases h : 0 < k ∧ k < n
    · rw [ite_eq_left h, ite_eq_left h]
      have hc : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hkN)
      have hn0 : (n - 1 : ℕ) ≠ 0 := by omega
      have hnR : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      field_simp
    · simp only [ite_eq_right h, mul_zero]
  have hsum := colless_payoff_sum_root_splits n hn
  rw [sum_congr rfl (fun A _ => colless_root_split_size_payoff n hn A),
    ← powerset_univ, sum_powerset] at hsum
  simp only [card_univ, Fintype.card_fin] at hsum
  change (∑ k ∈ range (n + 1), ∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
    if 0 < A.card ∧ A.card < n then
      (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) * f A.card else 0) =
    2 * collessExpected n at hsum
  rw [sum_congr rfl hbycard, ← sum_filter] at hsum
  have hi : (range (n + 1)).filter (fun k => 0 < k ∧ k < n) = Ico 1 n := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hi, ← mul_sum] at hsum
  change collessExpected n = (1 : ℝ) / (n - 1 : ℕ) * ∑ k ∈ Ico 1 n, f k
  rw [div_eq_mul_inv] at hsum ⊢
  nlinarith
end Rhone.Coalescent
