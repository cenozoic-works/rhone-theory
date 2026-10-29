/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeChronology

/-!
# Temporal coverage of the SMC′ regraft

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open scoped BigOperators

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_temporal_cover {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ)
    (hT : TreeNormalized T) (hc : TreeChronology T)
    (ht : 0 ≤ t) (hta : t ≤ a)
    (hs : s ∈ timeClades T t) (hs0 : s ≠ ∅) (hs1 : s ≠ Finset.univ)
    (ha : target ∈ timeClades T a) :
    TreeTemporalCover (regraft T s target t a) := by
  classical
  let F (c : Finset (Fin N)) := (c \ s) ∪ if (c ∩ target).Nonempty then s else ∅
  let l := (((List.finRange T.1).map (fun i => belowCut (T.2 i) t)) ++
    ((List.finRange T.1).map (fun i => betweenCutAttachment (T.2 i) s t a)) ++
    ((List.finRange T.1).map (fun i => aboveAttachment (T.2 i) s target a)) ++
    [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a])
  have hrootcut : t < rootHeight T := by
    by_contra hn
    have hr : rootHeight T ≤ t := le_of_not_gt hn
    simp only [timeClades, hr, ↓reduceIte, Finset.mem_singleton] at hs
    exact hs1 hs
  have hN : 0 < N := by
    obtain ⟨i, _⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    exact Nat.zero_lt_of_lt i.isLt
  have hmono (c d : Finset (Fin N)) (hcd : c ⊆ d) : F c ⊆ F d := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨hcd (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
    · by_cases hct : (c ∩ target).Nonempty
      · have hdt : (d ∩ target).Nonempty := by
          obtain ⟨j, hj⟩ := hct
          exact ⟨j, Finset.mem_inter.mpr ⟨hcd (Finset.mem_inter.mp hj).1,
            (Finset.mem_inter.mp hj).2⟩⟩
        simp only [hct, ↓reduceIte] at hi
        exact Finset.mem_union_right _ (by simpa only [hdt, ↓reduceIte] using hi)
      · simp [hct] at hi
  have hfinite (c : Finset (Fin N)) (lo hi q : ℝ) (hc0 : c ≠ ∅)
      (hc1 : c ≠ Finset.univ) (hlo : lo ≤ q) (hhi : q < hi) :
      0 < branchLength (finiteBranch c lo hi) ∧
      (finiteBranch c lo hi).2.1 ≤ q ∧ q < (finiteBranch c lo hi).2.2 := by
    have hlh : lo < hi := hlo.trans_lt hhi
    simp only [finiteBranch, not_or.mpr ⟨hc0, hc1⟩, ↓reduceIte,
      max_eq_right hlh.le, branchLength, max_eq_right (sub_nonneg.mpr hlh.le)]
    exact ⟨sub_pos.mpr hlh, hlo, hhi⟩
  have hactive (b : Branch N) (hb : b ∈ l) (q : ℝ)
      (hp : 0 < branchLength b ∧ b.2.1 ≤ q ∧ q < b.2.2) :
      (activeBranches (regraft T s target t a) q).Nonempty := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
    refine ⟨i, ?_⟩
    change i ∈ activeBranches (treeOfList l) q
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change 0 < branchLength (l.get i) ∧ (l.get i).2.1 ≤ q ∧ q < (l.get i).2.2
    rw [hi]
    exact hp
  have hbelow (i : Fin T.1) : belowCut (T.2 i) t ∈ l := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, by simp, rfl⟩))))))
  have habove (i : Fin T.1) : aboveAttachment (T.2 i) s target a ∈ l := by
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨i, by simp, rfl⟩))))
  have hnew : finiteBranch s t a ∈ l := by
    exact List.mem_append.mpr (Or.inr (by simp))
  have hproper (b : Branch N) (hp : 0 < branchLength b) :
      b.1 ≠ ∅ ∧ b.1 ≠ Finset.univ := by
    by_cases hc : b.1 = ∅ ∨ b.1 = Finset.univ
    · simp [branchLength, hc] at hp
    · exact not_or.mp hc
  have hpos (c : Finset (Fin N)) (lo hi : ℝ)
      (hp : 0 < branchLength (finiteBranch c lo hi)) :
      lo < hi ∧ (finiteBranch c lo hi).2.2 = hi := by
    obtain ⟨hc0, hc1⟩ := hproper _ hp
    change c ≠ ∅ at hc0
    change c ≠ Finset.univ at hc1
    have hlh : lo < hi := by
      by_contra hn
      simp [finiteBranch, branchLength, hc0, hc1, max_eq_left (le_of_not_gt hn)] at hp
    exact ⟨hlh, by simp [finiteBranch, hc0, hc1, max_eq_right hlh.le]⟩
  intro q hq hqr
  by_cases hqt : q < t
  · obtain ⟨i, hi⟩ := tree_chronology_temporal_cover T hN hc q hq (hqt.trans hrootcut)
    simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hc0, hc1⟩ := hproper _ hi.1
    exact hactive _ (hbelow i) q
      (hfinite _ _ _ q hc0 hc1 hi.2.1 (lt_min hi.2.2 hqt))
  · have htq : t ≤ q := le_of_not_gt hqt
    by_cases hqa : q < a
    · exact hactive _ hnew q (hfinite s t a q hs0 hs1 htq hqa)
    · have haq : a ≤ q := le_of_not_gt hqa
      have hex : ∃ i : Fin (regraft T s target t a).1,
          0 < branchLength ((regraft T s target t a).2 i) ∧
          q < ((regraft T s target t a).2 i).2.2 := by
        by_contra hn
        push Not at hn
        have hfold (v : List ℝ) (hv : ∀ z ∈ v, z ≤ q) : v.foldr max 0 ≤ q := by
          induction v with
          | nil => exact hq
          | cons z rest ih =>
            exact max_le (hv z (by simp)) (ih (fun w hw => hv w (by simp [hw])))
        have hr : rootHeight (regraft T s target t a) ≤ q := by
          apply hfold
          intro z hz
          rcases List.mem_map.mp hz with ⟨i, _, rfl⟩
          split_ifs with hp
          · exact hn i hp
          · exact hq
        exact not_le.mpr hqr hr
      obtain ⟨i, hip, hiq⟩ := hex
      have himem : (regraft T s target t a).2 i ∈ l := List.get_mem _ i
      have hfuture : ∃ r d, q ≤ r ∧ d ∈ timeClades T r ∧
          (F d).Nonempty ∧ F d ≠ Finset.univ := by
        simp only [l, List.mem_append, List.mem_map, List.mem_cons,
          List.not_mem_nil, or_false] at himem
        rcases himem with ((⟨j, _, hj⟩ | ⟨j, _, hj⟩) | ⟨j, _, hj⟩) | (hj | hj)
        · rw [← hj] at hip hiq
          have hh := (hpos _ _ _ hip).2
          have hb : (belowCut (T.2 j) t).2.2 ≤ t := by
            exact hh.trans_le (min_le_right _ _)
          linarith
        · rw [← hj] at hip hiq
          have hh := (hpos _ _ _ hip).2
          have hb : (betweenCutAttachment (T.2 j) s t a).2.2 ≤ a := by
            exact hh.trans_le (min_le_right _ _)
          linarith
        · rw [← hj] at hip hiq
          have hends := hpos _ _ _ hip
          change max (T.2 j).2.1 a < (T.2 j).2.2 ∧ _ at hends
          have hbhi : q < (T.2 j).2.2 := by
            change q < (finiteBranch (F (T.2 j).1) (max (T.2 j).2.1 a) (T.2 j).2.2).2.2 at hiq
            rwa [hends.2] at hiq
          let r := max (T.2 j).2.1 q
          have hrhi : r < (T.2 j).2.2 :=
            max_lt ((le_max_left _ _).trans_lt hends.1) hbhi
          have holdpos : 0 < branchLength (T.2 j) := by
            have hcj : ¬ ((T.2 j).1 = ∅ ∨ (T.2 j).1 = Finset.univ) := by
              intro hcj
              linarith [(hT j).2 hcj, le_max_left (T.2 j).2.1 a]
            simp [branchLength, hcj,
              max_eq_right (sub_nonneg.mpr ((le_max_left _ _).trans hends.1.le)),
              sub_pos.mpr ((le_max_left _ _).trans_lt hends.1)]
          have hrroot : r < rootHeight T := hrhi.trans_le (branch_hi_le_root T j holdpos)
          refine ⟨r, (T.2 j).1, le_max_right _ _, ?_, ?_, ?_⟩
          · simp only [timeClades, not_le.mpr hrroot, ↓reduceIte, Finset.mem_image]
            exact ⟨j, by
              simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨holdpos, le_max_left _ _, hrhi⟩, rfl⟩
          · have hp := (hproper _ hip).1
            exact Finset.nonempty_iff_ne_empty.mpr hp
          · exact (hproper _ hip).2
        · rw [hj] at hip hiq
          have hh := (hpos _ _ _ hip).2
          linarith
        · rw [hj] at hip hiq
          have hh := (hpos _ _ _ hip).2
          linarith
      obtain ⟨r, d, hqr', hdr, hfd0, hfd1⟩ := hfuture
      obtain ⟨y, hy⟩ := hfd0
      have hcurrent : ∃ c ∈ timeClades T q, (F c).Nonempty ∧ F c ≠ Finset.univ := by
        by_cases hys : y ∈ s
        · have hdt : (d ∩ target).Nonempty := by
            by_contra hn
            simp only [F, hn, ↓reduceIte, Finset.union_empty, Finset.mem_sdiff] at hy
            exact hy.2 hys
          obtain ⟨z, hz⟩ := hdt
          obtain ⟨c, hcq, hzc⟩ := (hc.1 q hq).2.1 z
          have hcd : c ⊆ d := chronology_clade_subset_of_intersection T hc q r hq hqr'
            c d hcq hdr ⟨z, Finset.mem_inter.mpr ⟨hzc, (Finset.mem_inter.mp hz).1⟩⟩
          have hct : (c ∩ target).Nonempty :=
            ⟨z, Finset.mem_inter.mpr ⟨hzc, (Finset.mem_inter.mp hz).2⟩⟩
          refine ⟨c, hcq, ⟨y, Finset.mem_union_right _ ?_⟩, ?_⟩
          · simpa only [hct, ↓reduceIte] using hys
          · intro he
            apply hfd1
            apply Finset.eq_univ_of_forall
            intro z
            apply hmono c d hcd
            simp only [he, Finset.mem_univ]
        · have hyd : y ∈ d := by
            rcases Finset.mem_union.mp hy with hy | hy
            · exact (Finset.mem_sdiff.mp hy).1
            · split_ifs at hy <;> simp_all
          obtain ⟨c, hcq, hyc⟩ := (hc.1 q hq).2.1 y
          have hcd : c ⊆ d := chronology_clade_subset_of_intersection T hc q r hq hqr'
            c d hcq hdr ⟨y, Finset.mem_inter.mpr ⟨hyc, hyd⟩⟩
          refine ⟨c, hcq, ⟨y, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hyc, hys⟩)⟩, ?_⟩
          intro he
          apply hfd1
          apply Finset.eq_univ_of_forall
          intro z
          apply hmono c d hcd
          simp only [he, Finset.mem_univ]
      obtain ⟨c, hcq, hfc0, hfc1⟩ := hcurrent
      have hqroot : q < rootHeight T := by
        by_contra hn
        simp only [timeClades, le_of_not_gt hn, ↓reduceIte, Finset.mem_singleton] at hcq
        subst c
        have htarget0 := (hc.1 a (ht.trans hta)).1 target ha
        have hfull : F Finset.univ = Finset.univ := by
          have hint : (Finset.univ ∩ target).Nonempty := by
            simpa only [Finset.univ_inter] using Finset.nonempty_iff_ne_empty.mpr htarget0
          simp only [F, hint, ↓reduceIte]
          exact Finset.sdiff_union_of_subset (Finset.subset_univ s)
        exact hfc1 hfull
      simp only [timeClades, not_le.mpr hqroot, ↓reduceIte, Finset.mem_image] at hcq
      obtain ⟨j, hj, he⟩ := hcq
      simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hactive _ (habove j) q
        (hfinite (F (T.2 j).1) (max (T.2 j).2.1 a) (T.2 j).2.2 q
          (by simpa only [he] using Finset.nonempty_iff_ne_empty.mp hfc0)
          (by simpa only [he] using hfc1) (max_le hj.2.1 haq) hj.2.2)
end Rhone.Coalescent.SmcPrime
