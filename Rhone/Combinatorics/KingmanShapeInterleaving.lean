/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapes
public import Mathlib.Data.Fintype.Fin
/-!
# Chronological interleavings of two merger histories, counted by `C(a+b, a)`

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
def HistoryInterleaving (a b : ℕ) := {s : Finset (Fin (a + b)) // s.card = a}
noncomputable instance (a b : ℕ) : Fintype (HistoryInterleaving a b) := by
  unfold HistoryInterleaving
  exact Fintype.ofFinite _
def interleavingLeft {a b : ℕ} (s : HistoryInterleaving a b) (k : ℕ) : ℕ :=
  (s.1.filter (fun i => i.val < k)).card
def interleavingRight {a b : ℕ} (s : HistoryInterleaving a b) (k : ℕ) : ℕ :=
  (s.1ᶜ.filter (fun i => i.val < k)).card
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem card_historyInterleaving (a b : ℕ) :
    Fintype.card (HistoryInterleaving a b) = (a + b).choose a := by
  classical
  let e : HistoryInterleaving a b ≃ ((univ : Finset (Fin (a + b))).powersetCard a) :=
    { toFun := fun s => ⟨s.1, mem_powersetCard.mpr ⟨subset_univ _, s.2⟩⟩
      invFun := fun s => ⟨s.1, (mem_powersetCard.mp s.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
theorem interleavingLeft_le {a b : ℕ} (s : HistoryInterleaving a b) (k : ℕ) :
    interleavingLeft s k ≤ a := by
  exact (card_filter_le _ _).trans_eq s.2
theorem interleavingRight_le {a b : ℕ} (s : HistoryInterleaving a b) (k : ℕ) :
    interleavingRight s k ≤ b := by
  have hc : s.1ᶜ.card = b := by
    rw [card_compl, Fintype.card_fin, s.2]
    omega
  exact (card_filter_le _ _).trans_eq hc
theorem interleaving_counts_sum {a b : ℕ} (s : HistoryInterleaving a b)
    (k : ℕ) (hk : k ≤ a + b) : interleavingLeft s k + interleavingRight s k = k := by
  have he : s.1.filter (fun i => i.val < k) ∪ s.1ᶜ.filter (fun i => i.val < k) =
      univ.filter (fun i : Fin (a + b) => i.val < k) := by
    ext i
    simp only [mem_union, mem_filter, mem_compl, mem_univ, true_and]
    tauto
  have hd : Disjoint (s.1.filter (fun i => i.val < k))
      (s.1ᶜ.filter (fun i => i.val < k)) :=
    (disjoint_compl_right).mono (filter_subset _ _) (filter_subset _ _)
  rw [interleavingLeft, interleavingRight, ← card_union_of_disjoint hd, he,
    Fin.card_filter_val_lt, Nat.min_eq_right hk]
theorem interleaving_counts_zero {a b : ℕ} (s : HistoryInterleaving a b) :
    interleavingLeft s 0 = 0 ∧ interleavingRight s 0 = 0 := by
  simp [interleavingLeft, interleavingRight]
theorem interleaving_counts_end {a b : ℕ} (s : HistoryInterleaving a b) :
    interleavingLeft s (a + b) = a ∧ interleavingRight s (a + b) = b := by
  have hleft : interleavingLeft s (a + b) = a := by
    unfold interleavingLeft
    rw [filter_true_of_mem (fun (i : Fin (a + b)) _ => i.isLt)]
    exact s.2
  have hsum := interleaving_counts_sum s (a + b) le_rfl
  omega
private theorem shape_slot_count_succ {m : ℕ} (s : Finset (Fin m)) (k : Fin m) :
    (s.filter (fun i => i.val < k.val + 1)).card =
      if k ∈ s then (s.filter (fun i => i.val < k.val)).card + 1
      else (s.filter (fun i => i.val < k.val)).card := by
  by_cases hm : k ∈ s
  · rw [ite_eq_left hm]
    have he : s.filter (fun i => i.val < k.val + 1) =
        insert k (s.filter (fun i => i.val < k.val)) := by
      ext i
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hi, hk⟩
        by_cases he : i = k
        · exact Or.inl he
        · exact Or.inr ⟨hi, by have hn : i.val ≠ k.val := fun hv => he (Fin.ext hv); omega⟩
      · rintro (rfl | ⟨hi, hk⟩)
        · exact ⟨hm, by omega⟩
        · exact ⟨hi, by omega⟩
    rw [he, card_insert_of_notMem (by simp)]
  · rw [ite_eq_right hm]
    congr 1
    ext i
    simp only [mem_filter]
    constructor
    · rintro ⟨hi, hk⟩
      have he : i ≠ k := fun he => hm (he ▸ hi)
      exact ⟨hi, by have hn : i.val ≠ k.val := fun hv => he (Fin.ext hv); omega⟩
    · rintro ⟨hi, hk⟩
      exact ⟨hi, by omega⟩
theorem finite_slot_count_succ {m : ℕ} (s : Finset (Fin m)) (k : Fin m) :
    (s.filter (fun i => i.val < k.val + 1)).card =
      if k ∈ s then (s.filter (fun i => i.val < k.val)).card + 1
      else (s.filter (fun i => i.val < k.val)).card :=
  shape_slot_count_succ s k
theorem interleaving_counts_succ {a b : ℕ} (s : HistoryInterleaving a b) (k : Fin (a + b)) :
    if k ∈ s.1 then
      interleavingLeft s (k.val + 1) = interleavingLeft s k.val + 1 ∧
      interleavingRight s (k.val + 1) = interleavingRight s k.val
    else
      interleavingLeft s (k.val + 1) = interleavingLeft s k.val ∧
      interleavingRight s (k.val + 1) = interleavingRight s k.val + 1 := by
  have hl := shape_slot_count_succ s.1 k
  have hr := shape_slot_count_succ s.1ᶜ k
  by_cases hm : k ∈ s.1
  · simp only [hm, mem_compl, not_true_eq_false, ite_true, ite_false] at hl hr ⊢
    exact ⟨hl, hr⟩
  · simp only [hm, mem_compl, not_false_eq_true, ite_true, ite_false] at hl hr ⊢
    exact ⟨hl, hr⟩
end Rhone.Combinatorics
