/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentBudget
public import Rhone.Coalescent.SmcPrimeProposalKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Finite boundary intervals of the attachment search

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess

noncomputable def attachmentBoundaries {N : ℕ} (T : Tree N) : Finset ℝ := by
  classical
  exact insert (rootHeight T)
    (((List.finRange T.1).flatMap (fun i => [(T.2 i).2.1, (T.2 i).2.2])).toFinset)

theorem next_boundary_strict {N : ℕ} (T : Tree N) (t : ℝ)
    (ht : t < rootHeight T) : t < nextBoundary T t := by
  have h (l : List ℝ) : t < l.foldr (fun b a => if t < b then min b a else a)
      (rootHeight T) := by
    induction l with
    | nil => exact ht
    | cons b rest ih =>
      simp only [List.foldr]
      split_ifs with hb
      · exact lt_min hb ih
      · exact ih
  exact h _

theorem next_boundary_mem {N : ℕ} (T : Tree N) (t : ℝ) :
    nextBoundary T t ∈ attachmentBoundaries T := by
  classical
  have h (l : List ℝ) : l.foldr (fun b a => if t < b then min b a else a)
      (rootHeight T) ∈ insert (rootHeight T) l.toFinset := by
    induction l with
    | nil => simp
    | cons b rest ih =>
      simp only [List.foldr]
      split_ifs with hb
      · by_cases hba : b ≤ rest.foldr (fun b a => if t < b then min b a else a)
            (rootHeight T)
        · simp [min_eq_left hba]
        · rw [min_eq_right (le_of_not_ge hba)]
          simpa [Finset.mem_insert, or_assoc, or_left_comm] using Or.inr ih
      · simpa [Finset.mem_insert, or_assoc, or_left_comm] using Or.inr ih
  exact h _

theorem next_boundary_le_endpoint {N : ℕ} (T : Tree N) (t b : ℝ)
    (hb : b ∈ attachmentBoundaries T) (htb : t < b) :
    nextBoundary T t ≤ b := by
  classical
  have h (l : List ℝ) : ∀ b ∈ insert (rootHeight T) l.toFinset, t < b →
      l.foldr (fun b a => if t < b then min b a else a) (rootHeight T) ≤ b := by
    induction l with
    | nil =>
      intro b hb _
      have he : b = rootHeight T := by simpa using hb
      subst b
      exact le_rfl
    | cons a rest ih =>
      intro b hb htb
      have hb' : b = rootHeight T ∨ b = a ∨ b ∈ rest.toFinset := by simpa using hb
      simp only [List.foldr]
      by_cases hta : t < a
      · rw [ite_eq_left hta]
        rcases hb' with hb' | hb' | hb'
        · exact (min_le_right _ _).trans (ih b (Finset.mem_insert.mpr (Or.inl hb')) htb)
        · simp [hb']
        · exact (min_le_right _ _).trans (ih b (Finset.mem_insert.mpr (Or.inr hb')) htb)
      · rw [ite_eq_right hta]
        rcases hb' with hb' | hb' | hb'
        · exact ih b (Finset.mem_insert.mpr (Or.inl hb')) htb
        · subst b; exact False.elim (hta htb)
        · exact ih b (Finset.mem_insert.mpr (Or.inr hb')) htb
  exact h _ b hb htb

theorem attachment_boundaries_card {N : ℕ} (T : Tree N) :
    (attachmentBoundaries T).card ≤ 2 * T.1 + 1 := by
  classical
  unfold attachmentBoundaries
  apply (Finset.card_insert_le _ _).trans
  have hl : (((List.finRange T.1).flatMap
      (fun i => [(T.2 i).2.1, (T.2 i).2.2])).length) = 2 * T.1 := by
    simp [List.length_flatMap, Nat.mul_comm]
  have hc := List.toFinset_card_le (((List.finRange T.1).flatMap
    (fun i => [(T.2 i).2.1, (T.2 i).2.2])))
  omega

theorem activeBranches_eq_before_boundary {N : ℕ} (T : Tree N) (t s : ℝ)
    (ht : t < rootHeight T) (hs : t ≤ s) (hsb : s < nextBoundary T t) :
    activeBranches T s = activeBranches T t := by
  classical
  have _ := ht
  ext i
  have hlo : (T.2 i).2.1 ∈ attachmentBoundaries T := by
    apply Finset.mem_insert_of_mem
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨i, by simp, Or.inl rfl⟩
  have hhi : (T.2 i).2.2 ∈ attachmentBoundaries T := by
    apply Finset.mem_insert_of_mem
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨i, by simp, Or.inr rfl⟩
  have hlow : (T.2 i).2.1 ≤ s ↔ (T.2 i).2.1 ≤ t := by
    constructor
    · intro h
      by_contra hnt
      have := next_boundary_le_endpoint T t _ hlo (lt_of_not_ge hnt)
      linarith
    · exact fun h => h.trans hs
  have hhigh : s < (T.2 i).2.2 ↔ t < (T.2 i).2.2 := by
    constructor
    · exact fun h => hs.trans_lt h
    · intro h
      have := next_boundary_le_endpoint T t _ hhi h
      exact hsb.trans_le this
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, hlow, hhigh]

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachmentRate_eq_before_boundary {N : ℕ} (T : Tree N) (t s : ℝ)
    (ht : t < rootHeight T) (hs : t ≤ s) (hsb : s < nextBoundary T t) :
    attachmentRate T s = attachmentRate T t := by
  have hsr : s < rootHeight T :=
    hsb.trans_le (next_boundary_bounds T t ht.le).2
  simp only [attachmentRate, not_le.mpr hsr, not_le.mpr ht, ↓reduceIte,
    activeBranches_eq_before_boundary T t s ht hs hsb]
end Rhone.Coalescent.SmcPrime
