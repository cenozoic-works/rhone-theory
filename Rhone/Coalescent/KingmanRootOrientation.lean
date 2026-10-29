/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootPair
/-!
# Fair orientation of the two root children of a population genealogy

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem root_split_iff_root_child {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) (A : Finset L) :
    ADR11.roots (G.erase univ) = {A, univ \ A} ↔
      A ∈ ADR11.roots (G.erase univ) := by
  obtain ⟨B, _, _, hr⟩ := binary_hierarchy_root_pair G hG hL
  constructor
  · intro he
    rw [he]
    exact mem_insert_self _ _
  · intro hm
    rw [hr, mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hr
    · have hc : univ \ (univ \ B) = B := by ext x; simp
      rw [hc, pair_comm]
      exact hr
noncomputable def orientedRootSideMass (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  ∑ h : Combinatorics.RankedLabelledHistory n,
    Combinatorics.historyMass (ADR11.singletonForest n) (n - 1) h *
      (if A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) then 1 / 2 else
            0)
theorem oriented_root_side_mass (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA0 : 0 < A.card) (hAn : A.card < n) :
    orientedRootSideMass n A = 1 / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) := by
  have hm : orientedRootSideMass n A = rootSplitMass n A * (1 / 2) := by
    unfold orientedRootSideMass rootSplitMass
    rw [sum_mul]
    apply sum_congr rfl
    intro h hh
    have he := root_split_iff_root_child _
        (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h)
      (by simpa using hn) A
    simp only [he]
    split_ifs <;> simp
  rw [hm, root_split_mass n hn A hA0 hAn]
  ring
theorem oriented_root_side_size (n k : ℕ) (hn : 2 ≤ n)
    (hk0 : 1 ≤ k) (hkn : k < n) :
    (∑ A ∈ (univ : Finset (Fin n)).powersetCard k,
      orientedRootSideMass n A) = 1 / (n - 1 : ℕ) := by
  have hs : ∀ A ∈ (univ : Finset (Fin n)).powersetCard k,
      orientedRootSideMass n A = 1 / ((n - 1 : ℕ) * (n.choose k : ℝ)) := by
    intro A hA
    have ha := (mem_powersetCard.mp hA).2
    rw [oriented_root_side_mass n hn A (by omega) (by omega), ha]
  rw [sum_congr rfl hs, sum_const, nsmul_eq_mul, card_powersetCard,
    card_univ, Fintype.card_fin]
  have hc : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  field_simp
end Rhone.Coalescent
