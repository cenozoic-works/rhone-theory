/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeInterleaving
/-!
# Selected merger slots determine every retained compressed rank

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem finite_slot_count_mono {t : ℕ} (s : Finset (Fin t))
    (k l : ℕ) (hkl : k ≤ l) :
    (s.filter (fun i => i.val < k)).card ≤ (s.filter (fun i => i.val < l)).card := by
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨(mem_filter.mp hi).1, lt_of_lt_of_le (mem_filter.mp hi).2 hkl⟩
theorem finite_slot_count_range {t : ℕ} (s : Finset (Fin t)) (j : ℕ) (hj : j ≤ s.card) :
    ∃ k ≤ t, (s.filter (fun i => i.val < k)).card = j := by
  let c := fun k => (s.filter (fun i => i.val < k)).card
  have range (l : ℕ) (hl : l ≤ t) : ∀ j ≤ c l, ∃ k ≤ l, c k = j := by
    induction l with
    | zero =>
      intro j hj
      have hz : c 0 = 0 := by simp [c]
      exact ⟨0, le_rfl, by omega⟩
    | succ l ih =>
      intro j hj
      by_cases he : j ≤ c l
      · obtain ⟨k, hk, hkj⟩ := ih (by omega) j he
        exact ⟨k, by omega, hkj⟩
      · refine ⟨l+1, le_rfl, ?_⟩
        have hc := finite_slot_count_succ s ⟨l, by omega⟩
        dsimp only at hc
        change c (l+1) = if _ then c l + 1 else c l at hc
        split at hc
        · rw [hc] at hj ⊢
          exact Nat.le_antisymm (Nat.succ_le_of_lt (Nat.lt_of_not_ge he)) hj
        · exact False.elim (he (hc ▸ hj))
  apply range t le_rfl j
  simpa only [c, filter_true_of_mem (fun (i : Fin t) _ => i.isLt)] using hj
theorem finite_slot_count_transition {t : ℕ} (s : Finset (Fin t))
    (j : ℕ) (hj : j < s.card) :
    ∃ k : Fin t, (s.filter (fun i => i.val < k.val)).card = j ∧
      (s.filter (fun i => i.val < k.val+1)).card = j+1 := by
  let c := fun k => (s.filter (fun i => i.val < k)).card
  obtain ⟨l, hl, he⟩ := finite_slot_count_range s (j+1) (by omega)
  have find (l : ℕ) (hl : l ≤ t) (he : c l = j+1) :
      ∃ k : Fin t, c k.val = j ∧ c (k.val+1) = j+1 := by
    induction l with
    | zero =>
      have hz : c 0 = 0 := by simp [c]
      omega
    | succ l ih =>
      have hc := finite_slot_count_succ s ⟨l, by omega⟩
      dsimp only at hc
      change c (l+1) = if _ then c l + 1 else c l at hc
      by_cases hcj : c l = j+1
      · exact ih (by omega) hcj
      · refine ⟨⟨l, by omega⟩, ?_, he⟩
        dsimp only
        split at hc
        · exact Nat.add_right_cancel (hc.symm.trans he)
        · exact False.elim (hcj (hc.symm.trans he))
  exact find l hl he
theorem finite_slot_snapshot_eq {α : Type*} {t : ℕ} (s : Finset (Fin t)) (p : ℕ → α)
    (hstep : ∀ k : Fin t, k ∉ s → p (k.val+1) = p k.val)
    (k l : ℕ) (hk : k ≤ t) (hl : l ≤ t)
    (he : (s.filter (fun i => i.val < k)).card =
      (s.filter (fun i => i.val < l)).card) : p k = p l := by
  let c := fun k => (s.filter (fun i => i.val < k)).card
  have ordered (k l : ℕ) (hl : l ≤ t) (hkl : k ≤ l) (he : c k = c l) : p k = p l := by
    induction l generalizing k with
    | zero =>
      have hk0 : k = 0 := by omega
      exact congrArg p hk0
    | succ l ih =>
      by_cases hke : k = l+1
      · exact congrArg p hke
      · have hkle : k ≤ l := by omega
        have hmono := finite_slot_count_mono s k l hkle
        have hc := finite_slot_count_succ s ⟨l, by omega⟩
        dsimp only at hc
        change c (l+1) = if _ then c l + 1 else c l at hc
        have hn : (⟨l, by omega⟩ : Fin t) ∉ s := by
          intro hm
          rw [ite_eq_left hm] at hc
          change c k ≤ c l at hmono
          omega
        rw [ite_eq_right hn] at hc
        exact (ih k (by omega) hkle (he.trans hc)).trans (hstep ⟨l, by omega⟩ hn).symm
  rcases le_total k l with hkl | hlk
  · exact ordered k l hl hkl he
  · exact (ordered l k hk hlk he.symm).symm
end Rhone.Combinatorics
