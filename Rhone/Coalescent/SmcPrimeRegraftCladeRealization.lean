/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftActiveClades

/-!
# Branch realization of proper clades in each regraft time range

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def RegraftCladeAt {N : ℕ} (T : Tree N) (s target : Finset (Fin N))
    (t a q : ℝ) (c : Finset (Fin N)) : Prop :=
  (q < t ∧ c ∈ timeClades T q) ∨
  (t ≤ q ∧ q < a ∧ (c = s ∨ ∃ d ∈ timeClades T q, c = d \ s)) ∨
  (a ≤ q ∧ ∃ d ∈ timeClades T q, c = regraftClade s target d)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_clade_at_active {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a q : ℝ) (c : Finset (Fin N))
    (htarget : target ≠ ∅) (hc0 : c ≠ ∅) (hc1 : c ≠ Finset.univ)
    (hform : RegraftCladeAt T s target t a q c) :
    ∃ i ∈ activeBranches (regraft T s target t a) q,
      ((regraft T s target t a).2 i).1 = c := by
  classical
  let l := (((List.finRange T.1).map (fun i => belowCut (T.2 i) t)) ++
    ((List.finRange T.1).map (fun i => betweenCutAttachment (T.2 i) s t a)) ++
    ((List.finRange T.1).map (fun i => aboveAttachment (T.2 i) s target a)) ++
    [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a])
  have hfinite (lo hi : ℝ) (hlo : lo ≤ q) (hhi : q < hi)
      (hb : finiteBranch c lo hi ∈ l) :
      ∃ i ∈ activeBranches (regraft T s target t a) q,
        ((regraft T s target t a).2 i).1 = c := by
    have hlh : lo < hi := hlo.trans_lt hhi
    have hp : 0 < branchLength (finiteBranch c lo hi) ∧
        (finiteBranch c lo hi).2.1 ≤ q ∧ q < (finiteBranch c lo hi).2.2 := by
      simp only [finiteBranch, not_or.mpr ⟨hc0, hc1⟩, ↓reduceIte,
        max_eq_right hlh.le, branchLength, max_eq_right (sub_nonneg.mpr hlh.le)]
      exact ⟨sub_pos.mpr hlh, hlo, hhi⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
    refine ⟨i, ?_, ?_⟩
    · change i ∈ activeBranches (treeOfList l) q
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change 0 < branchLength (l.get i) ∧ (l.get i).2.1 ≤ q ∧ q < (l.get i).2.2
      rwa [hi]
    · change (l.get i).1 = c
      rw [hi]
      rfl
  have hbelow (i : Fin T.1) : belowCut (T.2 i) t ∈ l := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, by simp, rfl⟩))))))
  have hmiddle (i : Fin T.1) : betweenCutAttachment (T.2 i) s t a ∈ l := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨i, by simp, rfl⟩))))))
  have habove (i : Fin T.1) : aboveAttachment (T.2 i) s target a ∈ l := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨i, by simp, rfl⟩))))
  rcases hform with ⟨hqt, hcq⟩ | ⟨htq, hqa, hform⟩ | ⟨haq, d, hdq, hcd⟩
  · have hr : q < rootHeight T := by
      by_contra hn
      simp only [timeClades, le_of_not_gt hn, ↓reduceIte, Finset.mem_singleton] at hcq
      exact hc1 hcq
    simp only [timeClades, not_le.mpr hr, ↓reduceIte, Finset.mem_image] at hcq
    obtain ⟨i, hi, he⟩ := hcq
    simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply hfinite _ _ hi.2.1 (lt_min hi.2.2 hqt)
    simpa only [belowCut, he] using hbelow i
  · rcases hform with hcs | ⟨d, hdq, hcd⟩
    · apply hfinite t a htq hqa
      exact List.mem_append.mpr (Or.inr (by simp [hcs]))
    · by_cases hr : rootHeight T ≤ q
      · have hdu : d = Finset.univ := by
          simpa only [timeClades, hr, ↓reduceIte, Finset.mem_singleton] using hdq
        apply hfinite (rootHeight T) a hr hqa
        exact List.mem_append.mpr (Or.inr (by simp [hcd, hdu]))
      · simp only [timeClades, hr, ↓reduceIte, Finset.mem_image] at hdq
        obtain ⟨i, hi, he⟩ := hdq
        simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        apply hfinite _ _ (max_le hi.2.1 htq) (lt_min hi.2.2 hqa)
        simpa only [betweenCutAttachment, he, ← hcd] using hmiddle i
  · by_cases hr : rootHeight T ≤ q
    · have hdu : d = Finset.univ := by
        simpa only [timeClades, hr, ↓reduceIte, Finset.mem_singleton] using hdq
      have hfull : regraftClade s target Finset.univ = Finset.univ := by
        have hint : (Finset.univ ∩ target).Nonempty := by
          simpa only [Finset.univ_inter] using Finset.nonempty_iff_ne_empty.mpr htarget
        change Finset.univ \ s ∪ (if (Finset.univ ∩ target).Nonempty then s else ∅) = _
        rw [ite_eq_left hint]
        exact Finset.sdiff_union_of_subset (Finset.subset_univ s)
      exact False.elim (hc1 (hcd.trans (hdu ▸ hfull)))
    · simp only [timeClades, hr, ↓reduceIte, Finset.mem_image] at hdq
      obtain ⟨i, hi, he⟩ := hdq
      simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply hfinite _ _ (max_le hi.2.1 haq) hi.2.2
      have hb := habove i
      change finiteBranch (regraftClade s target (T.2 i).1) _ _ ∈ l at hb
      simpa only [he, ← hcd] using hb

end Rhone.Coalescent.SmcPrime
