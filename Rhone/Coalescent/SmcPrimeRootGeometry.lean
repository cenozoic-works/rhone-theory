/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeLengthGeometry

/-!
# Root height bounds for clipped SMC′ regrafts

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem root_height_le_of_branch_bounds {N : ℕ} (U : Tree N) (M : ℝ) (hM : 0 ≤ M)
      (hU : ∀ i, 0 < branchLength (U.2 i) → (U.2 i).2.2 ≤ M) :
    rootHeight U ≤ M := by
  have hfold (l : List ℝ) (hl : ∀ v ∈ l, v ≤ M) : l.foldr max 0 ≤ M := by
    induction l with
    | nil => exact hM
    | cons v rest ih => exact max_le (hl v (by simp)) (ih (fun w hw => hl w (by simp [hw])))
  apply hfold
  intro v hv
  rcases List.mem_map.mp hv with ⟨i, _, rfl⟩
  split_ifs with hi
  · exact hU i hi
  · exact hM

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_root_height_le {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ) (hT : TreeNormalized T)
    (_ht : t ≤ rootHeight T) (_hta : t ≤ a) :
    rootHeight (regraft T s target t a) ≤ max (rootHeight T) a := by
  classical
  have hpos (c : Finset (Fin N)) (lo hi : ℝ)
      (hp : 0 < branchLength (finiteBranch c lo hi)) :
      lo < hi ∧ (finiteBranch c lo hi).2.2 = hi := by
    by_cases hc : c = ∅ ∨ c = Finset.univ
    · simp [branchLength, finiteBranch, hc] at hp
    · have hl : lo < hi := by
        by_contra hn
        simp [branchLength, finiteBranch, hc, max_eq_left (le_of_not_gt hn)] at hp
      exact ⟨hl, by simp [finiteBranch, hc, max_eq_right hl.le]⟩
  have hold (i : Fin T.1) (c : Finset (Fin N)) (lo hi : ℝ)
      (hlo : (T.2 i).2.1 ≤ lo) (hhi : hi ≤ (T.2 i).2.2)
      (hp : 0 < branchLength (finiteBranch c lo hi)) :
      (finiteBranch c lo hi).2.2 ≤ rootHeight T := by
    obtain ⟨hl, he⟩ := hpos c lo hi hp
    have hd : (T.2 i).2.1 < (T.2 i).2.2 := lt_of_le_of_lt hlo (hl.trans_le hhi)
    have hc : ¬ ((T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ) := by
      intro hc
      linarith [(hT i).2 hc]
    have hb : 0 < branchLength (T.2 i) := by
      simp [branchLength, hc, max_eq_right (sub_nonneg.mpr hd.le), sub_pos.mpr hd]
    rw [he]
    exact hhi.trans (branch_hi_le_root T i hb)
  have hbranch : ∀ b ∈
      (((List.finRange T.1).map (fun j => belowCut (T.2 j) t)) ++
        ((List.finRange T.1).map (fun j => betweenCutAttachment (T.2 j) s t a)) ++
        ((List.finRange T.1).map (fun j => aboveAttachment (T.2 j) s target a)) ++
        [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a]),
      0 < branchLength b → b.2.2 ≤ max (rootHeight T) a := by
    intro b hb hp
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with ((⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩) | (rfl | rfl)
    · exact (hold i _ _ _ le_rfl (min_le_left _ _) hp).trans (le_max_left _ _)
    · exact (hold i _ _ _ (le_max_left _ _) (min_le_left _ _) hp).trans (le_max_left _ _)
    · exact (hold i _ _ _ (le_max_left _ _) le_rfl hp).trans (le_max_left _ _)
    · rw [(hpos _ _ _ hp).2]
      exact le_max_right _ _
    · rw [(hpos _ _ _ hp).2]
      exact le_max_right _ _
  apply root_height_le_of_branch_bounds _ _ ((root_height_nonneg T).trans (le_max_left _ _))
  intro i hi
  exact hbranch _ (List.get_mem _ i) hi

end Rhone.Coalescent.SmcPrime
