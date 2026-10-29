/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeActiveUnique
public import Rhone.Coalescent.SmcPrimeRegraftCladePartitions
public import Mathlib.Data.List.Pairwise
/-!
# Activity of individual branch-array entries of the old and regrafted trees

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

def BranchActive {N : ℕ} (b : Branch N) (q : ℝ) : Prop :=
  0 < branchLength b ∧ b.2.1 ≤ q ∧ q < b.2.2

theorem finite_branch_active_iff {N : ℕ} (c : Finset (Fin N)) (lo hi q : ℝ) :
    BranchActive (finiteBranch c lo hi) q ↔
      c ≠ ∅ ∧ c ≠ Finset.univ ∧ lo ≤ q ∧ q < hi := by
  classical
  by_cases hc : c = ∅ ∨ c = Finset.univ
  · simp only [BranchActive, finiteBranch, hc, ↓reduceIte, branchLength]
    rcases hc with rfl | rfl <;> simp
  · have hc0 := (not_or.mp hc).1
    have hc1 := (not_or.mp hc).2
    by_cases hhi : lo ≤ hi
    · simp only [BranchActive, finiteBranch, ↓reduceIte, max_eq_right hhi,
        branchLength, hc0, hc1, false_or, ↓reduceIte,
        max_eq_right (sub_nonneg.mpr hhi), sub_pos]
      constructor
      · intro h; exact ⟨hc0, hc1, h.2.1, h.2.2⟩
      · intro h; exact ⟨h.2.2.1.trans_lt h.2.2.2, h.2.2.1, h.2.2.2⟩
    · have hlt : hi < lo := lt_of_not_ge hhi
      simp only [BranchActive, finiteBranch, ↓reduceIte, max_eq_left hlt.le,
        branchLength, hc0, hc1, false_or, ↓reduceIte, sub_self, max_self, lt_self_iff_false,
        false_and]
      constructor
      · intro h; contradiction
      · intro h; linarith [h.2.2.1, h.2.2.2]

theorem branch_active_of_normalized_bounds {N : ℕ} (T : Tree N)
    (hnorm : TreeNormalized T) (i : Fin T.1) (q : ℝ)
    (hlo : (T.2 i).2.1 ≤ q) (hhi : q < (T.2 i).2.2) :
    BranchActive (T.2 i) q := by
  have hd := hlo.trans_lt hhi
  have hc : ¬ ((T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ) := by
    intro h
    linarith [(hnorm i).2 h]
  exact ⟨by simp [branchLength, hc, max_eq_right (sub_nonneg.mpr hd.le),
    sub_pos.mpr hd], hlo, hhi⟩

theorem branch_active_time_clade {N : ℕ} (T : Tree N) (q : ℝ)
    (i : Fin T.1) (hi : BranchActive (T.2 i) q) : (T.2 i).1 ∈ timeClades T q := by
  have hr : q < rootHeight T := hi.2.2.trans_le (branch_hi_le_root T i hi.1)
  simp only [timeClades, not_le.mpr hr, ↓reduceIte, Finset.mem_image]
  exact ⟨i, by simpa [activeBranches, BranchActive] using hi, rfl⟩

theorem below_cut_active {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (t q : ℝ) (i : Fin T.1) (hi : BranchActive (belowCut (T.2 i) t) q) :
    BranchActive (T.2 i) q ∧ q < t := by
  have hh := (finite_branch_active_iff _ _ _ _).mp hi
  exact ⟨branch_active_of_normalized_bounds T hnorm i q hh.2.2.1
    (lt_min_iff.mp hh.2.2.2).1, (lt_min_iff.mp hh.2.2.2).2⟩

theorem between_cut_active {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (s : Finset (Fin N)) (t a q : ℝ) (i : Fin T.1)
    (hi : BranchActive (betweenCutAttachment (T.2 i) s t a) q) :
    BranchActive (T.2 i) q ∧ t ≤ q ∧ q < a ∧ (T.2 i).1 \ s ≠ ∅ := by
  have hh := (finite_branch_active_iff _ _ _ _).mp hi
  exact ⟨branch_active_of_normalized_bounds T hnorm i q
    ((le_max_left _ _).trans hh.2.2.1) (lt_min_iff.mp hh.2.2.2).1,
    (le_max_right _ _).trans hh.2.2.1, (lt_min_iff.mp hh.2.2.2).2, hh.1⟩

theorem above_attachment_active {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (s target : Finset (Fin N)) (a q : ℝ) (i : Fin T.1)
    (hi : BranchActive (aboveAttachment (T.2 i) s target a) q) :
    BranchActive (T.2 i) q ∧ a ≤ q ∧ regraftClade s target (T.2 i).1 ≠ ∅ := by
  have hh := (finite_branch_active_iff _ _ _ _).mp hi
  exact ⟨branch_active_of_normalized_bounds T hnorm i q
    ((le_max_left _ _).trans hh.2.2.1) hh.2.2.2,
    (le_max_right _ _).trans hh.2.2.1, hh.1⟩
end Rhone.Coalescent.SmcPrime
