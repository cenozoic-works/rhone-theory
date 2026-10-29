/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeChronology

/-!
# Finite endpoint epoch criterion for the chronology of finite tree arrays

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
noncomputable def treeEpochs {N : ℕ} (T : Tree N) : List ℝ :=
  [0, rootHeight T] ++ (List.finRange T.1).flatMap
    (fun i => [(T.2 i).2.1, (T.2 i).2.2])

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
noncomputable def epochPredecessor {N : ℕ} (T : Tree N) (q : ℝ) : ℝ :=
  (treeEpochs T).foldr (fun e p => if e ≤ q then max e p else p) 0

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem epoch_predecessor_bounds {N : ℕ} (T : Tree N) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ epochPredecessor T q ∧ epochPredecessor T q ≤ q ∧
      epochPredecessor T q ∈ treeEpochs T ∧
      ∀ e ∈ treeEpochs T, e ≤ q → e ≤ epochPredecessor T q := by
  have h (l : List ℝ) :
      0 ≤ l.foldr (fun e p => if e ≤ q then max e p else p) 0 ∧
      l.foldr (fun e p => if e ≤ q then max e p else p) 0 ≤ q ∧
      (l.foldr (fun e p => if e ≤ q then max e p else p) 0 = 0 ∨
        l.foldr (fun e p => if e ≤ q then max e p else p) 0 ∈ l) ∧
      ∀ e ∈ l, e ≤ q → e ≤ l.foldr (fun e p => if e ≤ q then max e p else p) 0 := by
    induction l with
    | nil => exact ⟨le_rfl, hq, Or.inl rfl, by simp⟩
    | cons e rest ih =>
      simp only [List.foldr_cons]
      by_cases he : e ≤ q
      · simp only [he, ↓reduceIte]
        refine ⟨ih.1.trans (le_max_right _ _), max_le he ih.2.1, ?_, ?_⟩
        · by_cases hep : e ≤ rest.foldr (fun e p => if e ≤ q then max e p else p) 0
          · rw [max_eq_right hep]
            rcases ih.2.2.1 with hz | hm
            · exact Or.inl hz
            · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
          · rw [max_eq_left (le_of_not_ge hep)]
            exact Or.inr (by simp)
        · intro d hd hdq
          rcases List.mem_cons.mp hd with rfl | hd
          · exact le_max_left _ _
          · exact (ih.2.2.2 d hd hdq).trans (le_max_right _ _)
      · simp only [he, ↓reduceIte]
        refine ⟨ih.1, ih.2.1, ?_, ?_⟩
        · rcases ih.2.2.1 with hz | hm
          · exact Or.inl hz
          · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
        · intro d hd hdq
          rcases List.mem_cons.mp hd with rfl | hd
          · exact False.elim (he hdq)
          · exact ih.2.2.2 d hd hdq
  obtain ⟨hp0, hpq, hpmem, hgreat⟩ := h (treeEpochs T)
  refine ⟨hp0, hpq, ?_, hgreat⟩
  rcases hpmem with hz | hm
  · change epochPredecessor T q = 0 at hz
    rw [hz]
    simp [treeEpochs]
  · exact hm

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem time_clades_epoch_predecessor {N : ℕ} (T : Tree N) (q : ℝ) (hq : 0 ≤ q) :
    timeClades T q = timeClades T (epochPredecessor T q) := by
  classical
  obtain ⟨_, hpq, _, hgreat⟩ := epoch_predecessor_bounds T q hq
  have hcmp (e : ℝ) (he : e ∈ treeEpochs T) : e ≤ q ↔ e ≤ epochPredecessor T q :=
    ⟨hgreat e he, fun h => h.trans hpq⟩
  have hroot := hcmp (rootHeight T) (by simp [treeEpochs])
  have hactive : activeBranches T q = activeBranches T (epochPredecessor T q) := by
    ext i
    have hlo := hcmp (T.2 i).2.1 (by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩))
    have hhi := hcmp (T.2 i).2.2 (by
      apply List.mem_append.mpr
      exact Or.inr (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩))
    have hstrict : q < (T.2 i).2.2 ↔ epochPredecessor T q < (T.2 i).2.2 := by
      rw [← not_le, ← not_le, hhi]
    simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, hlo, hstrict]
  unfold timeClades
  by_cases hr : rootHeight T ≤ q
  · simp [hr, hroot.mp hr]
  · have hrp : ¬ rootHeight T ≤ epochPredecessor T q := fun h => hr (hroot.mpr h)
    simp [hr, hrp, hactive]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeChronologyEpochs {N : ℕ} (T : Tree N) : Prop :=
  (∀ q ∈ treeEpochs T, 0 ≤ q →
    (∀ c ∈ timeClades T q, c ≠ ∅) ∧
    (∀ i : Fin N, ∃ c ∈ timeClades T q, i ∈ c) ∧
    (∀ c ∈ timeClades T q, ∀ d ∈ timeClades T q, c ≠ d → Disjoint c d)) ∧
  (∀ q ∈ treeEpochs T, ∀ r ∈ treeEpochs T, 0 ≤ q → q ≤ r →
    ∀ c ∈ timeClades T q, ∃ d ∈ timeClades T r, c ⊆ d)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tree_chronology_iff_epochs {N : ℕ} (T : Tree N) :
    TreeChronology T ↔ TreeChronologyEpochs T := by
  constructor
  · intro h
    exact ⟨fun q _ hq => h.1 q hq, fun q _ r _ hq hqr => h.2 q r hq hqr⟩
  · intro h
    constructor
    · intro q hq
      obtain ⟨hp0, _, hpmem, _⟩ := epoch_predecessor_bounds T q hq
      rw [time_clades_epoch_predecessor T q hq]
      exact h.1 _ hpmem hp0
    · intro q r hq hqr c hcq
      obtain ⟨hp0, hpq, hpmem, _⟩ := epoch_predecessor_bounds T q hq
      obtain ⟨_, _, hrmem, hrgreat⟩ := epoch_predecessor_bounds T r (hq.trans hqr)
      have hpr : epochPredecessor T q ≤ epochPredecessor T r :=
        hrgreat _ hpmem (hpq.trans hqr)
      rw [time_clades_epoch_predecessor T q hq] at hcq
      obtain ⟨d, hd, hcd⟩ := h.2 _ hpmem _ hrmem hp0 hpr c hcq
      refine ⟨d, ?_, hcd⟩
      rwa [time_clades_epoch_predecessor T r (hq.trans hqr)]

end Rhone.Coalescent.SmcPrime
